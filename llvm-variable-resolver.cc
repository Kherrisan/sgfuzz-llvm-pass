#include "llvm-variable-resolver.h"
#include "llvm-variable-type.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/BinaryFormat/Dwarf.h"

#include <regex>
#include <optional>

#include "utils.h"

namespace pingu
{
    VarInfoResolver::VarInfoResolver()
    {
    }

    VarInfoResolver::~VarInfoResolver()
    {
    }

    std::optional<VarInfo> VarInfoResolver::interpret(llvm::Module *M, llvm::Type *type, VarInfo var)
    {
        // type can only be primitive type or vector type (<2 x i32>)
        assert(!type->isStructTy() && "type must not be a struct type");
        assert(!type->isArrayTy() && "type must not be an array type");

        if (type->isPointerTy())
        {
            return var;
        }

        if (!var.type)
        {
            return var;
        }

        auto opType = Type::fromType(M, type);
        if (!opType)
        {
            // unrecognized operation type
            // like: <2 x i32>
            dbgs() << "[!] sgfuzz-llvm-pass: unrecognized operation type: " << *type << "\n";
            return std::nullopt;
        }
        if (opType->kind() == Type::Kind::Struct)
        {
            auto structType = static_cast<Struct *>(opType);
            opType = Type::fromName(structType->name());
        }
        ENV_DEBUG(dbgs() << "interpret opType: " << opType->toString() << ", var: " << var.type->toString() << "\n");

        if (type->isVectorTy())
        {
            return std::nullopt;
        }

        if (var.type->isIndexable())
        {
            auto indexedType = static_cast<IndexedType *>(var.type);
            if (indexedType->isFromType(opType) && indexedType->kind() == IndexedType::Kind::Struct)
            {
                auto structType = static_cast<Struct *>(indexedType);
                indexedType = static_cast<Struct *>(Type::fromName(structType->name()));
            }
            std::vector<Member> memberRefs;
            // TODO: empty name
            std::string name;
            auto interpretedType = indexedType->interpreteAs(opType, memberRefs, name);
            if (interpretedType)
            {
                VarInfo interpretedVar = var;
                interpretedVar.type = interpretedType;
                if (memberRefs.size() > 0)
                {
                    std::unique_ptr<VarInfo> lastMember;
                    std::unique_ptr<VarInfo> targetMember;
                    for (int i = memberRefs.size() - 1; i >= 0; i--)
                    {
                        auto member = std::make_unique<VarInfo>();
                        member->name = std::get<0>(memberRefs.at(i));
                        member->type = std::get<1>(memberRefs.at(i));
                        member->is_local = var.is_local;
                        member->is_global = var.is_global;
                        member->is_param = var.is_param;

                        if (!lastMember)
                        {
                            targetMember = std::make_unique<VarInfo>(*member);
                        }
                        else
                        {
                            lastMember->parent = std::make_unique<VarInfo>(*member);
                        }

                        lastMember = std::move(member);
                    }

                    return *targetMember;
                }
                return interpretedVar;
            }
        }
        else
        {
            return var;
        }

        return std::nullopt;
    }

    void collectDICompositeTypes(llvm::DIType *Type, std::set<llvm::DIType *> &visited, std::map<std::string, llvm::DIType *> &map)
    {
        if (!Type || visited.count(Type))
            return;
        visited.insert(Type);

        if (auto *CT = llvm::dyn_cast<llvm::DICompositeType>(Type))
        {
            if (!CT->getName().empty())
            {
                if (map.find(CT->getName().str()) == map.end() || !CT->isForwardDecl())
                {
                    map[CT->getName().str()] = CT;
                }
            }
            for (auto *Element : CT->getElements())
            {
                if (auto *Member = llvm::dyn_cast<llvm::DIDerivedType>(Element))
                {
                    collectDICompositeTypes(Member->getBaseType(), visited, map);
                }
            }
            if (CT->getTag() == llvm::dwarf::DW_TAG_array_type)
            {
                collectDICompositeTypes(CT->getBaseType(), visited, map);
            }
        }
        else if (auto *DT = llvm::dyn_cast<llvm::DIDerivedType>(Type))
        {
            collectDICompositeTypes(DT->getBaseType(), visited, map);
        }
    }

    void VarInfoResolver::collectDIRetainedTypes(llvm::Module &M)
    {
        llvm::NamedMDNode *CUNode = M.getNamedMetadata("llvm.dbg.cu");
        assert(CUNode);

        for (llvm::MDNode *Node : CUNode->operands())
        {
            llvm::DICompileUnit *CU = llvm::dyn_cast<llvm::DICompileUnit>(Node);
            if (!CU)
                continue;

            for (llvm::DIScope *DS : CU->getRetainedTypes())
            {
                llvm::DIType *DT = llvm::dyn_cast<llvm::DIType>(DS);
                if (!DT)
                    continue;
                ENV_DEBUG(dbgs() << "collectDIRetainedTypes: " << DT->getName().str() << ", type: " << getDITypeString(DT) << "\n");
                Type::fromDIType(DT);
            }
        }
    }

    void VarInfoResolver::collectGlobalVars(llvm::Module &M)
    {
        // 收集结构体类型信息
        std::set<llvm::DIType *> visited;
        for (const llvm::Function &F : M)
        {
            if (llvm::DISubprogram *SP = F.getSubprogram())
            {
                // 收集函数参数和局部变量的类型信息
                for (const auto &BB : F)
                {
                    for (const auto &I : BB)
                    {
                        if (const llvm::DbgDeclareInst *DDI = llvm::dyn_cast<llvm::DbgDeclareInst>(&I))
                        {
                            if (llvm::DILocalVariable *DIVar = DDI->getVariable())
                            {
                                ENV_DEBUG(dbgs() << "collectGlobalVars DbgDeclareInst: " << DIVar->getName().str() << ", type: " << getDITypeString(DIVar->getType()) << "\n");
                                Type::fromDIType(DIVar->getType());
                            }
                        }
                    }
                }
            }
        }

        // 收集全局变量信息
        for (llvm::GlobalVariable &GV : M.globals())
        {
            if (auto *DGV = GV.getMetadata("dbg"))
            {
                if (auto *DVE = llvm::dyn_cast<llvm::DIGlobalVariableExpression>(DGV))
                {
                    ENV_DEBUG(dbgs() << "collectGlobalVars DIGlobalVariableExpression: " << DVE->getVariable()->getName().str() << ", type: " << getDITypeString(DVE->getVariable()->getType()) << "\n");
                    auto DG = DVE->getVariable();
                    VarInfo info;
                    info.name = DG->getName().str();
                    auto gvType = Type::fromDIType(DG->getType());
                    info.type = Type::fromTypeID(new Pointer(gvType));
                    info.is_global = true;
                    info.is_local = false;
                    info.is_param = false;
                    valueVarInfoCache[&GV] = info;
                    ENV_DEBUG(ENV_DEBUG(dbgs() << "collecting global: " << DG->getName().str() << "\n"));
                }
            }
        }

        collectDIRetainedTypes(M);

        // Print collected struct types
        ENV_DEBUG(dbgs() << "Collected global variable struct types:\n");
        // for (const auto &[name, type] : structDITypes)
        // {
        //     ENV_DEBUG(dbgs() << "  " << name << ": " << getDITypeString(type) << "\n");
        // }
    }

    // 收集函数内的局部变量声明信息
    void VarInfoResolver::collectFunctionLocalVars(llvm::Function &F)
    {
        for (BasicBlock &BB : F)
        {
            for (Instruction &I : BB)
            {
                if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I))
                {
                    VarInfo info;
                    info.name = instructionValueName(AI);
                    auto M = AI->getParent()->getParent()->getParent();
                    auto allocaTy = Type::fromType(M, AI->getAllocatedType());
                    info.type = Type::fromTypeID(new Pointer(allocaTy));
                    info.is_local = true;
                    info.is_param = false;
                    info.is_global = false;
                    valueVarInfoCache[AI] = info;
                }
                else if (auto *DI = llvm::dyn_cast<llvm::DbgDeclareInst>(&I))
                {
                    if (auto *AI = dyn_cast<llvm::AllocaInst>(DI->getAddress()))
                    {
                        VarInfo info;
                        info.name = DI->getVariable()->getName().str();
                        info.type = Type::fromDIType(DI->getVariable()->getType());
                        info.type = Type::fromTypeID(new Pointer(info.type));
                        info.is_local = true;
                        info.is_param = false;
                        info.is_global = false;
                        valueVarInfoCache[AI] = info;
                        // ENV_DEBUG(dbgs() << "collectFunctionLocalVars: " << *AI << " -> " << info.type->toString() << "\n");
                    }
                }
                else if (auto *AI = llvm::dyn_cast<llvm::DbgAssignIntrinsic>(&I))
                {
                    if (auto *V = AI->getAddress())
                    {
                        VarInfo info;
                        info.name = AI->getVariable()->getName().str();
                        auto assignType = Type::fromDIType(AI->getVariable()->getType());
                        if (auto allocType = llvm::dyn_cast<llvm::AllocaInst>(V))
                        {
                            info.type = Type::fromTypeID(new Pointer(assignType));
                        }
                        else
                        {
                            info.type = assignType;
                        }
                        auto exprMeta = llvm::cast<llvm::MetadataAsValue>(AI->getArgOperand(2))->getMetadata();
                        if (auto expr = llvm::dyn_cast<llvm::DIExpression>(exprMeta))
                        {
                            ENV_DEBUG(dbgs() << "DbgAssignIntrinsic, DIExpression: " << *expr << "\n");
                            if (expr->getNumElements() > 0 && expr->getElement(0) == llvm::dwarf::DW_OP_LLVM_fragment)
                            {
                                // auto valueName = instructionValueName(AI->getArgOperand(4));
                                // int offset = expr->getElement(1);
                                // int width = expr->getElement(2);
                                // ENV_DEBUG(dbgs() << "DbgAssignIntrinsic, DW_OP_LLVM_fragment, valueName: " << valueName << ", offset: " << offset << ", width: " << width << "\n");
                                // std::vector<Member> memberRefs;
                                // auto fieldType = static_cast<IndexedType *>(assignType)->index(width, offset, memberRefs, valueName);
                                // auto field = join(info, memberRefs);
                                continue;
                            }
                        }
                        info.is_local = true;
                        info.is_param = false;
                        info.is_global = false;
                        valueVarInfoCache[V] = info;
                        // ENV_DEBUG(dbgs() << "collectFunctionLocalVars: " << *AI << " -> " << info.type->toString() << "\n");
                    }
                }
                else if (auto *VI = llvm::dyn_cast<llvm::DbgValueInst>(&I))
                {
                    // 对于 llvm.dbg.value
                    if (auto *V = VI->getValue())
                    {
                        VarInfo info;
                        info.name = VI->getVariable()->getName().str();
                        info.type = Type::fromDIType(VI->getVariable()->getType());
                        if (auto allocType = llvm::dyn_cast<llvm::AllocaInst>(V))
                        {
                            info.type = Type::fromTypeID(new Pointer(info.type));
                        }
                        info.is_local = true;
                        info.is_param = false;
                        info.is_global = false;
                        valueVarInfoCache[V] = info;
                        // ENV_DEBUG(dbgs() << "collectFunctionLocalVars: " << *VI << " -> " << info.type->toString() << "\n");
                    }
                }
            }
        }
    }

    void VarInfoResolver::collectDITypes(llvm::Module &M)
    {
        collectGlobalVars(M);
        for (auto &F : M.functions())
        {
            collectFunctionParams(F);
            if (F.empty())
            {
                continue;
            }
            collectFunctionLocalVars(F);
        }
    }

    void VarInfoResolver::collectFunctionParams(llvm::Function &F)
    {
        if (llvm::DISubprogram *SP = F.getSubprogram())
        {
            if (auto *subRoutineType = llvm::dyn_cast<llvm::DISubroutineType>(SP->getType()))
            {
                auto typeArray = subRoutineType->getTypeArray();
                int argOffset = typeArray.size() - F.arg_size();
                for (unsigned i = argOffset; i < typeArray.size() && (i - argOffset) < F.arg_size(); ++i)
                {
                    VarInfo info;
                    info.name = F.getArg(i - argOffset)->getName().str();
                    ENV_DEBUG(dbgs() << "collectFunctionParams: " << F.getName() << ", paramDIType: " << getDITypeString(typeArray[i]) << "\n");
                    if (!typeArray[i])
                    {
                        info.type = &Void::VOID;
                    }
                    else if (auto *paramDIType = llvm::dyn_cast<llvm::DIType>(typeArray[i]))
                    {
                        info.type = Type::fromDIType(paramDIType);
                        if (paramDIType->getFlags() & llvm::DINode::DIFlags::FlagTypePassByValue)
                        {
                            info.type = Type::fromTypeID(new Pointer(info.type));
                        }
                    }
                    info.is_param = true;
                    info.is_local = false;
                    info.is_global = false;
                    ENV_DEBUG(dbgs() << "collectFunctionParams: " << info.name << " " << info.type->toString() << "\n");
                    valueVarInfoCache[F.getArg(i - argOffset)] = info;
                }
            }
        }
    }

    std::optional<VarInfo> VarInfoResolver::join(VarInfo &parent, std::vector<Member> &memberRefs)
    {
        ENV_DEBUG(dbgs() << "join: " << parent.type->toString() << "\n");
        ENV_DEBUG(dbgs() << "with: \n");
        for (auto &[name, type] : memberRefs)
        {
            ENV_DEBUG(dbgs() << "  " << name << ": " << type->toString() << "\n");
        }
        if (memberRefs.size() == 0)
        {
            return parent;
        }
        std::shared_ptr<VarInfo> lastMember;
        std::shared_ptr<VarInfo> targetMember;
        for (int i = memberRefs.size() - 1; i >= 0; i--)
        {
            auto member = std::make_shared<VarInfo>();
            member->name = std::get<0>(memberRefs[i]);
            member->type = std::get<1>(memberRefs[i]);
            member->is_local = parent.is_local;
            member->is_param = parent.is_param;
            member->is_global = parent.is_global;
            if (!lastMember)
            {
                targetMember = member;
            }
            else
            {
                lastMember->parent = member;
            }
            lastMember = member;
        }
        lastMember->parent = std::make_unique<VarInfo>(parent);
        if (parent.type->kind() == Type::Kind::Pointer)
        {
            lastMember->parent->type = static_cast<Pointer *>(parent.type)->pointee();
        }

        return *targetMember;
    }

    std::optional<Type *> VarInfoResolver::resolveBitfield(llvm::GetElementPtrInst *GEP, VarInfo *parent)
    {
        if (!parent)
        {
            return std::nullopt;
        }
        if (!GEP || GEP->getNumOperands() <= 2)
        {
            return std::nullopt;
        }
        auto CI = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(2));
        if (!CI)
        {
            return std::nullopt;
        }

        llvm::Instruction *bfLoad = nullptr;
        for (auto *user : GEP->users())
        {
            if (auto *load = llvm::dyn_cast<llvm::LoadInst>(user))
            {
                bfLoad = load;
                break;
            }
        }
        if (!bfLoad)
        {
            return std::nullopt;
        }
        // auto bfLoad = GEP->getNextNonDebugInstruction();
        if (!bfLoad || bfLoad->getNumUses() <= 0)
        {
            return std::nullopt;
        }

        auto M = GEP->getParent()->getParent()->getParent();
        auto GEPSrcType = Type::fromType(M, GEP->getSourceElementType());
        ENV_DEBUG(dbgs() << "GEPSrcType: " << GEPSrcType->toString() << "\n");

        VarInfo parentPointee = *parent;
        parentPointee.type = static_cast<Pointer *>(parent->type)->pointee();
        if (parentPointee.type->isDeclaration())
        {
            auto name = parentPointee.type->name();
            parentPointee.type = Type::fromName(name);
            if (!parentPointee.type)
            {
                ENV_DEBUG(dbgs() << "Failed to find definition of: '" << name << "'\n");
                return std::nullopt;
            }
        }

        int offset = 0;

        auto bfLoadUser = llvm::dyn_cast<llvm::Instruction>(*bfLoad->user_begin());
        if (bfLoadUser && bfLoadUser->getOpcode() == llvm::Instruction::And)
        {
            llvm::Instruction *andInst = bfLoadUser;
            auto andMsk = andInst->getOperand(1);
            auto *CI = llvm::dyn_cast<llvm::ConstantInt>(andMsk);
            if (!CI)
            {
                return std::nullopt;
            }
            ENV_DEBUG(dbgs() << "Probe bfLoad: " << *bfLoad << "\n");
            ENV_DEBUG(dbgs() << "Probe andInst: " << *andInst << "\n");
            ENV_DEBUG(dbgs() << "Probe andMsk: " << *andMsk << "\n");
            int width = 0;
            int offset = 0;

            if (CI->getValue().isNegative())
            {
                // and mask is like: 11111110, 11111100, 1111101
                // and mask is used to clear the bit fields, then set to some value (by OR)
                int trailingOnes = CI->getValue().countr_one();
                int consecutiveZeros = CI->getValue().getBitWidth() - CI->getValue().popcount();
                width = consecutiveZeros;
                offset = trailingOnes;
                ENV_DEBUG(dbgs() << "trailingOnes: " << trailingOnes << ", consecutiveZeros: " << consecutiveZeros << "\n");
            }
            else
            {
                // and mask is like: 00000001, 00000011, 00000110
                // and mask is used to get the bit fields, and reference the value (used for CMP, ZEXT, etc)
                int trailingZeros = CI->getValue().countr_zero();
                int consecutiveOnes = CI->getValue().popcount();
                width = consecutiveOnes;
                offset = trailingZeros;
                ENV_DEBUG(dbgs() << "trailingZeros: " << trailingZeros << ", consecutiveOnes: " << consecutiveOnes << "\n");
            }
            ENV_DEBUG(dbgs() << "resolveBitfield, offset: " << offset << ", width: " << width << "\n");
            return Type::fromTypeID(new Bitfield(offset, width));
        }
        else if (bfLoadUser && bfLoadUser->getOpcode() == llvm::Instruction::LShr)
        {
            llvm::Instruction *lshr = bfLoadUser;
            auto lshrOffset = lshr->getOperand(1);
            if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(lshrOffset))
            {
                ENV_DEBUG(dbgs() << "Probe LShr: " << *lshr << "\n");
                offset = CI->getZExtValue();
                auto lshrUser = pruneBitfieldCasting(*lshr->user_begin());
                if (!lshrUser)
                {
                    ENV_DEBUG(dbgs() << "Unknown user of lshr when resolving bitfield width: " << *lshr << "\n");
                    assert(false);
                }
                auto andInst = llvm::dyn_cast<llvm::Instruction>(lshrUser);
                if (andInst->getOpcode() == llvm::Instruction::And)
                {
                    // auto andMsk = andInst->getOperand(1);
                    int width = CI->getValue().popcount();
                    return Type::fromTypeID(new Bitfield(offset, width));
                }
                else
                {
                    // 没有 and 在 lshr 之后
                    // 尝试简单推断，例如 i8 >> 7，那么 width 为 1
                    int width = llvm::dyn_cast<llvm::LoadInst>(bfLoad)->getType()->getIntegerBitWidth() - CI->getZExtValue();
                    return Type::fromTypeID(new Bitfield(offset, width));
                }
            }
            else
            {
                return std::nullopt;
            }
        }
        else
        {
            return std::nullopt;
        }

        return std::nullopt;
    }

    std::optional<VarInfo> VarInfoResolver::resolveGEP(llvm::GetElementPtrInst *GEP)
    {
        auto parent = resolveVarInfo(GEP->getPointerOperand(), GEP->getParent()->getParent());
        if (!parent)
        {
            return std::nullopt;
        }

        auto bitfieldTy = resolveBitfield(GEP, &*parent);

        auto M = GEP->getParent()->getParent()->getParent();
        auto gepSrcType = Type::fromType(M, GEP->getSourceElementType());
        ENV_DEBUG(dbgs() << "resolveGEP parent: " << parent->type->toString() << "\n");
        auto parentPtrType = dynamic_cast<Pointer *>(parent->type);
        auto resolvedType = parentPtrType ? parentPtrType->pointee() : parent->type;
        if (resolvedType->isDeclaration() || Type::isFromType(resolvedType))
        {
            std::string name = resolvedType->name();
            resolvedType = Type::fromName(name);
            if (!resolvedType)
            {
                dbgs() << "[!] sgfuzz-llvm-pass: Failed to find definition of: '" << name << "'\n";
                return std::nullopt;
            }
        }
        assert(resolvedType);
        std::vector<Member> memberRefs;
        auto gepValueName = instructionValueName(GEP);
        if (GEP->getNumOperands() >= 2)
        {
            // resolve the first index
            auto CI = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
            int index = 0;
            if (CI)
            {
                index = CI->getZExtValue();
            }
            else
            {
                // TODO:
                // non-constant index in GEP
                // require the gepSrcType and resolvedType's element type are the same size
                // int resolvedElemTySz;
                // if (resolvedT)
            }
            ENV_DEBUG(dbgs() << "resolveGEP operand 1 index: " << index << "\n");
            assert(resolvedType);
            if (resolvedType->isIndexable())
            {
                // For example:
                // GEP i32, i32* %0, 8
                //     => gepSrcType is i32[9], resolvedType is i32[9]
                //     => index the 8th i32 of gepSrcType in the resolvedType i32[9]
                // GEP i32[8], i32[8]* %0, 8
                //     => gepSrcType is i32[8][9], resolvedType is i32[8][9]
                //     => index the 8th i32[8] of gepSrcType in the resolvedType i32[8][1]
                if (resolvedType->isDeclaration() || Type::isFromType(resolvedType))
                {
                    auto name = resolvedType->name();
                    resolvedType = Type::fromName(name);
                    if (!resolvedType)
                    {
                        ENV_DEBUG(dbgs() << "Failed to find definition of: '" << name << "'\n");
                        assert(false);
                    }
                }
                gepSrcType = Type::fromTypeID(new Array(gepSrcType, index + 1));
                resolvedType = Type::fromTypeID(new Array(resolvedType, index + 1));
                std::vector<Member> memberRefs;
                auto resolvedFieldType = static_cast<IndexedType *>(resolvedType)->indexAs(gepSrcType, index, memberRefs, gepValueName);
                if (!resolvedFieldType)
                {
                    ENV_DEBUG(dbgs() << "[!] Failed to gep " << index << " of " << gepSrcType->toString() << ", in " << resolvedType->toString() << "\n");
                    return std::nullopt;
                }
                resolvedType = resolvedFieldType;
                auto gepSrcFieldType = static_cast<IndexedType *>(gepSrcType)->index(index);
                if (!gepSrcFieldType)
                {
                    ENV_DEBUG(dbgs() << "[!] Failed to index " << index << " in " << gepSrcType->toString() << "\n");
                    return std::nullopt;
                }
                gepSrcType = gepSrcFieldType;
            }
            else
            {
                resolvedType = gepSrcType;
            }
            ENV_DEBUG(dbgs() << "resolveGEP resolvedType: " << resolvedType->toString() << "\n");
        }
        if (GEP->getNumOperands() >= 3)
        {
            // resolve the second and the following indexes
            for (int i = 2; i < GEP->getNumOperands(); i++)
            {
                auto CI = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(i));
                int index = 0;
                if (CI)
                {
                    index = CI->getZExtValue();
                }
                ENV_DEBUG(dbgs() << "resolveGEP operand " << i << " index: " << index << "\n");
                if (resolvedType->isDeclaration() || (resolvedType->kind() == Type::Kind::Struct && Type::isFromType(resolvedType)))
                {
                    auto name = resolvedType->name();
                    auto typeDef = Type::fromName(name);
                    if (!typeDef)
                    {
                        ENV_DEBUG(dbgs() << "Failed to find definition of: '" << name << "'\n");
                    }
                    else
                    {
                        resolvedType = typeDef;
                    }
                }
                if (!resolvedType->isIndexable())
                {
                    dbgs() << "[!] sgfuzz-llvm-pass: Type is not indexable: '" << resolvedType->toString() << "'\n";
                    return std::nullopt;
                }
                // dbgs() << "resolvedType: " << resolvedType->toDebugJson().dump(4) << "\n";
                auto indexedType = static_cast<IndexedType *>(resolvedType);
                resolvedType = indexedType->indexAs(gepSrcType, index, memberRefs, gepValueName, bitfieldTy);
                if (!resolvedType)
                {
                    ENV_DEBUG(dbgs() << "[!] Failed to gep " << index << " of " << gepSrcType->toString() << ", in " << indexedType->toString() << "\n");
                    return std::nullopt;
                }
                gepSrcType = static_cast<IndexedType *>(gepSrcType)->index(index);
                if (!gepSrcType)
                {
                    ENV_DEBUG(dbgs() << "[!] Failed to index " << index << " in " << gepSrcType->toString() << "\n");
                    return std::nullopt;
                }
                if (resolvedType->kind() == Type::Kind::Union && i < GEP->getNumOperands() - 1)
                {
                    // union is only supported for the last index
                    return std::nullopt;
                }
            }
        }

        parent->type = parentPtrType ? parentPtrType->pointee() : parent->type;
        auto field = join(*parent, memberRefs);
        if (field)
        {
            VarInfo fieldPtr(*field);
            fieldPtr.type = Type::fromTypeID(new Pointer(field->type));
            ENV_DEBUG(dbgs() << "resolveGEP store to cache: " << *GEP << " -> type: " << fieldPtr.type->toString() << "\n");
            valueVarInfoCache[GEP] = fieldPtr;
            return fieldPtr;
        }
        return std::nullopt;
    }

    std::optional<VarInfo> VarInfoResolver::resolveLoad(llvm::LoadInst *LI)
    {
        auto F = LI->getParent()->getParent();
        auto M = F->getParent();
        auto ptrOperand = resolveVarInfo(LI->getPointerOperand(), F);
        if (!ptrOperand)
        {
            return std::nullopt;
        }
        auto ptrType = static_cast<Pointer *>(ptrOperand->type);
        assert(ptrType);
        assert(ptrType->pointee());
        auto opType = Type::fromType(M, LI->getType());
        if (!opType)
        {
            return std::nullopt;
        }
        std::vector<Member> memberRefs;
        Type *actualType = nullptr;
        std::string loadValueName = instructionValueName(LI);
        auto pointee = ptrType->pointee();
        ENV_DEBUG(dbgs() << "resolveLoad pointee: " << pointee->toString() << "\n");
        if (pointee->isDeclaration())
        {
            auto name = pointee->name();
            pointee = Type::fromName(name);
            if (!pointee)
            {
                dbgs() << "[!] sgfuzz-llvm-pass: Failed to find definition of: '" << name << "'\n";
                return std::nullopt;
            }
        }
        if (pointee->isIndexable())
        {
            actualType = static_cast<IndexedType *>(pointee)->interpreteAs(opType, memberRefs, loadValueName);
        }
        else
        {
            actualType = pointee->interpreteAs(opType, memberRefs, loadValueName);
        }
        if (!actualType)
        {
            return std::nullopt;
        }
        ENV_DEBUG(dbgs() << "interpreteAs: " << ptrType->pointee()->toString() << " -> " << actualType->toString() << "\n");
        if (memberRefs.size() > 0)
        {
            auto info = join(*ptrOperand, memberRefs);
            return info;
        }
        else
        {
            ptrOperand->type = actualType;
            return *ptrOperand;
        }
    }

    std::optional<VarInfo> VarInfoResolver::resolvePHI(llvm::PHINode *PN)
    {
        // 在 PHI 的多个 incoming value 中，选择最早定义，且在该 PHI 指令之前的 value
        // 如果所有 incoming value 都在该 PHI 之后定义，那么可能存在问题
        llvm::BasicBlock *BB = PN->getParent();
        llvm::Value *selectedIncomingValue = nullptr;
        auto F = PN->getParent()->getParent();
        for (auto &FBB : *F)
        {
            int FBBIndex = PN->getBasicBlockIndex(&FBB);
            if (FBBIndex != -1)
            {
                selectedIncomingValue = PN->getIncomingValue(FBBIndex);
                break;
            }
            else if (BB == &FBB)
            {
                return std::nullopt;
            }
        }
        if (auto incomingValueInfo = resolveVarInfo(selectedIncomingValue, F))
        {
            VarInfo info = *incomingValueInfo;
            valueVarInfoCache[PN] = info;
            ENV_DEBUG(dbgs() << "resolved phi: " << instructionValueName(PN) << ", name: " << info.name << ", type: " << info.type->toString() << "\n");
            return info;
        }

        return std::nullopt;
    }

    // 解析变量信息的主函数
    std::optional<VarInfo> VarInfoResolver::resolveVarInfo(llvm::Value *V, llvm::Function *F)
    {
        ENV_DEBUG(dbgs() << "resolveVarInfo: " << *V << "\n");
        if (valueVarInfoCache.find(V) != valueVarInfoCache.end())
        {
            auto var = valueVarInfoCache[V];
            ENV_DEBUG(dbgs() << "resolved from cache: " << var.name << " -> " << var.type->toString() << "\n");
            return var;
        }
        if (auto *ZEXT = llvm::dyn_cast<llvm::ZExtInst>(V))
        {
            auto var = resolveVarInfo(ZEXT->getOperand(0), F);
            if (var)
            {
                ENV_DEBUG(dbgs() << "resolved: " << *ZEXT << " -> type: " << var->type->toString() << "\n");
            }
            return var;
        }
        else if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(V))
        {
            auto var = resolveGEP(GEP);
            if (var)
            {
                ENV_DEBUG(dbgs() << "resolved: " << *GEP << " -> type: " << var->type->toString() << "\n");
            }
            return var;
        }
        else if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(V))
        {
            auto var = resolveLoad(LI);
            if (var)
            {
                ENV_DEBUG(dbgs() << "resolved: " << *LI << " -> type: " << var->type->toString() << "\n");
            }
            return var;
        }
        else if (auto *PHI = llvm::dyn_cast<llvm::PHINode>(V))
        {
            auto var = resolvePHI(PHI);
            if (var)
            {
                ENV_DEBUG(dbgs() << "resolved: " << *PHI << " -> type: " << var->type->toString() << "\n");
            }
            return var;
        }
        else
        {
            // Other instructions are not supported yet
            VarInfo info;
            info.name = instructionValueName(V);
            auto M = F->getParent();
            info.type = Type::fromType(M, V->getType());
            info.is_local = true;
            info.is_param = false;
            info.is_global = false;
            ENV_DEBUG(dbgs() << "resolved: " << *V << " -> type: " << info.type->toString() << "\n");
            return info;
        }
    }
}