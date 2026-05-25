// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#include "cangjie/CHIR/AST2CHIR/TranslateASTNode/Translator.h"

#include "cangjie/CHIR/Type/ExtendDef.h"
#include "cangjie/CHIR/UserDefinedType.h"
#include "cangjie/Mangle/CHIRTypeManglingUtils.h"
#include "cangjie/Utils/FileUtil.h"
#include "cangjie/Mangle/CHIRManglingUtils.h"

using namespace Cangjie::CHIR;
using namespace Cangjie;

namespace {
/**
 * DFS for a path from `cur` to `targetParent` (same ClassType object identity) in the inheritance graph.
 * On success, `outPath` is [target, ..., cur] with instantiated types.
 */
bool FindPathToTarget(ClassType& cur, ClassType& targetParent, CHIRBuilder& builder,
    const std::unordered_map<const GenericType*, Type*>& replaceTable, std::vector<ClassType*>& outPath,
    std::unordered_set<ClassType*>& onPath)
{
    if (&cur == &targetParent) {
        outPath.push_back(StaticCast<ClassType*>(ReplaceRawGenericArgType(cur, replaceTable, builder)));
        return true;
    }
    if (!onPath.insert(&cur).second) {
        return false;
    }

    auto unwindAndRecord =
        [&](ClassType& child, const std::unordered_map<const GenericType*, Type*>& childReplaceTable) {
        if (FindPathToTarget(child, targetParent, builder, childReplaceTable, outPath, onPath)) {
            outPath.push_back(StaticCast<ClassType*>(ReplaceRawGenericArgType(cur, replaceTable, builder)));
            return true;
        }
        return false;
    };

    for (auto ex : cur.GetCustomTypeDef()->GetExtends()) {
        // maybe we can meet `extend<T> A<B<T>> {}`, and `curType` is A<Int32>, then ignore this def,
        // so not need to check `res`
        auto [res, extendTable] = ex->GetExtendedType()->CalculateGenericTyMapping(cur);
        if (!res) {
            continue;
        }
        for (auto interface : ex->GetImplementedInterfaceTys()) {
            if (unwindAndRecord(*interface, extendTable)) {
                onPath.erase(&cur);
                return true;
            }
        }
    }
    for (auto interface : cur.GetImplementedInterfaceTys(&builder)) {
        if (unwindAndRecord(*interface, replaceTable)) {
            onPath.erase(&cur);
            return true;
        }
    }
    if (cur.GetSuperClassTy(&builder) != nullptr) {
        auto superClass = cur.GetSuperClassTy(&builder);
        if (unwindAndRecord(*superClass, replaceTable)) {
            onPath.erase(&cur);
            return true;
        }
    }
    onPath.erase(&cur);
    return false;
}

std::vector<ClassType*> GetTargetInheritanceList(CustomTypeDef& curDef, ClassType& targetParent, CHIRBuilder& builder)
{
    std::vector<ClassType*> path;
    std::unordered_set<ClassType*> onPath;
    std::unordered_map<const GenericType*, Type*> emptyTable;

    auto tryFrom = [&](ClassType& start) -> bool {
        path.clear();
        onPath.clear();
        return FindPathToTarget(start, targetParent, builder, emptyTable, path, onPath);
    };

    auto structTy = StaticCast<StructType*>(curDef.GetType());
    for (auto interface : structTy->GetImplementedInterfaceTys(&builder)) {
        if (tryFrom(*interface)) {
            return path;
        }
    }
    CJC_ASSERT(false);
    return path;
}

std::unordered_map<const GenericType*, Type*> CollectReplaceTable(
    CustomTypeDef& curDef, ClassType& targetParent, FuncBase* rawFunc, CHIRBuilder& builder)
{
    auto inheritanceList = GetTargetInheritanceList(curDef, targetParent, builder);
    std::unordered_map<const GenericType*, Type*> replaceTable;
    bool found = false;
    auto targetParentDef = rawFunc->GetParentCustomTypeDef();
    for (auto parent : inheritanceList) {
        if (parent->GetCustomTypeDef() != targetParentDef) {
            continue;
        }
        std::tie(found, replaceTable) = parent->GetCustomTypeDef()->GetType()->CalculateGenericTyMapping(*parent);
        CJC_ASSERT(found);
        break;
    }
    return replaceTable;
}
} // namespace

void Translator::CreateMutFuncWrapper(
    CHIRBuilder& builder, FuncBase* rawFunc, CustomTypeDef& curDef, ClassType& srcClassTy)
{
    // create the wrapper func
    auto replaceTable = CollectReplaceTable(curDef, srcClassTy, rawFunc, builder);

    auto instFuncTy = StaticCast<FuncType*>(ReplaceRawGenericArgType(*rawFunc->GetFuncType(), replaceTable, builder));
    auto wrapperParamsTy = instFuncTy->GetParamTypes();
    auto parentDefType = curDef.IsExtend() ? StaticCast<ExtendDef>(curDef).GetExtendedType() : curDef.GetType();
    wrapperParamsTy[0] = builder.GetType<RefType>(parentDefType);
    auto retTy = instFuncTy->GetReturnType();
    auto wrapperFuncTy = builder.GetType<FuncType>(wrapperParamsTy, retTy);

    auto funcIdentifier = CHIRMangling::GenerateVirtualFuncMangleName(rawFunc, curDef, &srcClassTy, false);
    auto pkgName = curDef.GetPackageName();

    bool isImported = curDef.TestAttr(Attribute::IMPORTED);
    FuncBase* funcBase = nullptr;
    if (isImported) {
        funcBase = builder.CreateImportedVarOrFunc<ImportedFunc>(wrapperFuncTy, funcIdentifier, "", "", pkgName);
    } else {
        funcBase = builder.CreateFunc(INVALID_LOCATION, wrapperFuncTy, funcIdentifier, "", "", pkgName);
    }
    CJC_NULLPTR_CHECK(funcBase);

    auto tempTy = StaticCast<RefType*>(instFuncTy->GetParamType(0))->GetBaseType();
    mutWrapperMap.Emplace(rawFunc, StaticCast<CustomType*>(parentDefType)->GetCustomTypeDef(), tempTy, funcBase);

    funcBase->Set<WrappedRawMethod>(rawFunc);
    funcBase->AppendAttributeInfo(rawFunc->GetAttributeInfo());
    funcBase->DisableAttr(Attribute::VIRTUAL);
    funcBase->EnableAttr(Attribute::NO_REFLECT_INFO);
    curDef.AddMethod(funcBase);

    if (isImported) {
        return;
    }

    auto func = DynamicCast<Func*>(funcBase);
    CJC_NULLPTR_CHECK(func);
    // create the func body
    BlockGroup* body = builder.CreateBlockGroup(*func);
    func->InitBody(*body);

    std::vector<Value*> args;
    for (auto paramTy : wrapperParamsTy) {
        args.emplace_back(builder.CreateParameter(paramTy, INVALID_LOCATION, *func));
    }

    auto entry = builder.CreateBlock(body);
    body->SetEntryBlock(entry);
    auto ret =
        Cangjie::CHIR::CreateAndAppendExpression<Allocate>(builder, builder.GetType<RefType>(retTy), retTy, entry);
    func->SetReturnValue(*ret->GetResult());

    // we should use the instantiated interface type here, but now we use `Any` as a workaround
    auto anyRefTy = builder.GetType<RefType>(builder.GetAnyTy());
    args[0] = Cangjie::CHIR::TypeCastOrBoxIfNeeded(*args[0], *anyRefTy, builder, *entry, INVALID_LOCATION);

    auto apply = Cangjie::CHIR::CreateAndAppendExpression<Apply>(builder, retTy, rawFunc, FuncCallContext{
        .args = args,
        .thisType = curDef.GetType()}, entry);
    Cangjie::CHIR::CreateAndAppendExpression<Store>(
        builder, builder.GetUnitTy(), apply->GetResult(), func->GetReturnValue(), entry);

    auto tempThis =
        Cangjie::CHIR::TypeCastOrBoxIfNeeded(*args[0], *wrapperParamsTy[0], builder, *entry, INVALID_LOCATION);
    auto load = Cangjie::CHIR::CreateAndAppendExpression<Load>(builder, parentDefType, tempThis, entry)->GetResult();
    auto structMemberTypes = StaticCast<StructType*>(parentDefType)->GetInstantiatedMemberTys(builder);

    for (size_t i = 0; i < structMemberTypes.size(); ++i) {
        auto path = std::vector<uint64_t>{i};
        auto field = Cangjie::CHIR::CreateAndAppendExpression<Field>(builder, structMemberTypes[i], load, path, entry)
            ->GetResult();
        Cangjie::CHIR::CreateAndAppendExpression<StoreElementRef>(
            builder, builder.GetUnitTy(), field, func->GetParam(0), path, entry);
    }

    entry->AppendExpression(builder.CreateTerminator<Exit>(entry));
}

void Translator::WrapperFuncContainer::Emplace(
    Value* rawFunc, CustomTypeDef* subDef, Type* parentTy, FuncBase* wrapperFunc)
{
    auto key = std::pair<Value*, CustomTypeDef*>{rawFunc, subDef};
    wrapperFuncs[key].emplace(parentTy, wrapperFunc);
}

FuncBase* Translator::WrapperFuncContainer::GetWrapperFunc(Value* rawFunc, CustomTypeDef* subDef, Type* parentTy) const
{
    auto key = std::pair<Value*, CustomTypeDef*>{rawFunc, subDef};
    auto it = wrapperFuncs.find(key);
    if (it == wrapperFuncs.end()) {
        return nullptr;
    }
    for (auto& typeIt : it->second) {
        if (TypeEqual(*typeIt.first, *parentTy)) {
            return typeIt.second;
        }
    }
    CJC_ABORT();
    return nullptr;
}

bool Translator::WrapperFuncContainer::TypeEqual(const Type& ty1, const Type& ty2) const
{
    if (&ty1 == &ty2) {
        return true;
    }
    if (ty1.IsGeneric() || ty2.IsGeneric()) {
        return true;
    }
    auto ty1Args = ty1.GetTypeArgs();
    auto ty2Args = ty2.GetTypeArgs();
    if (ty1Args.size() != ty2Args.size()) {
        return false;
    }
    if (ty1Args.empty()) {
        return false;
    }
    for (size_t i = 0; i < ty1Args.size(); ++i) {
        if (!TypeEqual(*ty1Args[i], *ty2Args[i])) {
            return false;
        }
    }
    return true;
}

void Translator::WrapMutFunc(CHIRBuilder& builder, CustomTypeDef& customTypeDef)
{
    Type* structTy = nullptr;
    if (customTypeDef.GetCustomKind() == CustomDefKind::TYPE_EXTEND &&
        StaticCast<ExtendDef>(customTypeDef).GetExtendedType()->IsStruct()) {
        structTy = StaticCast<ExtendDef>(customTypeDef).GetExtendedType();
    } else if (customTypeDef.GetCustomKind() == CustomDefKind::TYPE_STRUCT &&
        StaticCast<StructDef>(customTypeDef).GetImplementedInterfacesNum() > 0) {
        structTy = customTypeDef.GetType();
    }
    if (!structTy) {
        return;
    }
    for (auto& [srcTy, infos] : customTypeDef.GetVTable()) {
        for (size_t i = 0; i < infos.size(); ++i) {
            CJC_NULLPTR_CHECK(infos[i].instance);
            auto rawFunc = infos[i].instance;
            while (auto base = rawFunc->Get<WrappedRawMethod>()) {
                rawFunc = base;
            }
            if (!rawFunc->TestAttr(Attribute::MUT) || rawFunc->GetParentCustomTypeDef() == &customTypeDef) {
                continue;
            }
            if (auto ex = DynamicCast<ExtendDef*>(&customTypeDef);
                ex && ex->GetExtendedCustomTypeDef() == rawFunc->GetParentCustomTypeDef()) {
                continue;
            }
            CreateMutFuncWrapper(builder, rawFunc, customTypeDef, *StaticCast<ClassType*>(srcTy));
        }
    }
}