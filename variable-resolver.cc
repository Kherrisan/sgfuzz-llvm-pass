#include "variable-resolver.h"

#include "llvm/IR/DebugInfo.h"

#include "llvm/BinaryFormat/Dwarf.h"

#include <regex>
#include <optional>

std::string getDITypeString(DIType *ty);

DIDerivedType *findFirstOffsetDIType(DICompositeType *CT, int offset = 0)
{
    for (int i = 0; i < CT->getElements().size(); i++)
    {
        auto elem = CT->getElements()[i];
        if (auto derived = dyn_cast<DIDerivedType>(elem))
        {
            if (derived->getFlags() & DIType::DIFlags::FlagVirtual)
            {
                continue;
            }
            if (derived->getOffsetInBits() == offset)
            {
                if (derived->getName().find("_vptr$") == 0)
                {
                    continue;
                }
                else
                {
                    ENV_DEBUG(dbgs() << "findFirstOffsetDIType: " << getDITypeString(derived) << "\n");
                    return derived;
                }
            }
        }
    }
    return nullptr;
}

bool isEmptyClass(DIType *ty)
{
    if (ty->getTag() == dwarf::DW_TAG_inheritance)
    {
        ty = dyn_cast<DICompositeType>(ty)->getBaseType();
    }
    return dyn_cast<DICompositeType>(ty)->getSizeInBits() == 8;
}

int getTypeSizeInBits(Module *M, Type *ty)
{
    if (ty->isPointerTy())
    {
        return 64;
    }
    else if (ty->isStructTy())
    {
        DataLayout DL(M);
        const StructLayout *SL = DL.getStructLayout(dyn_cast<StructType>(ty));
        return SL->getSizeInBits();
    }
    else if (ty->isArrayTy())
    {
        int elemSize = getTypeSizeInBits(M, ty->getArrayElementType());
        return elemSize * ty->getArrayNumElements();
    }
    else
    {
        return ty->getPrimitiveSizeInBits();
    }
}

bool lastFieldIsPaddingField(Type *ty)
{
    if (ty->getStructNumElements() == 0)
    {
        return false;
    }
    auto lastField = ty->getStructElementType(ty->getStructNumElements() - 1);
    if (lastField->isArrayTy())
    {
        lastField = lastField->getArrayElementType();
    }
    if (lastField->isIntegerTy() && lastField->getIntegerBitWidth() == 8)
    {
        return true;
    }
    return false;
}

std::optional<std::string> resolveTypedefName(DIType *ty)
{
    while (ty)
    {
        if (auto *DITy = dyn_cast<DIDerivedType>(ty))
        {
            if (DITy->getTag() == dwarf::DW_TAG_typedef || DITy->getTag() == dwarf::DW_TAG_const_type || DITy->getTag() == dwarf::DW_TAG_member || DITy->getTag() == dwarf::DW_TAG_volatile_type || DITy->getTag() == dwarf::DW_TAG_enumeration_type)
            {
                if (DITy->getTag() == dwarf::DW_TAG_typedef)
                {
                    return DITy->getName().str();
                }
                else
                {
                    ty = DITy->getBaseType();
                }
            }
            else
            {
                break;
            }
        }
        else
        {
            break;
        }
    }
    return std::nullopt;
}

std::string getStructName(const std::string &structName)
{
    std::string name = structName;
    if (name.rfind("struct.", 0) == 0)
    {
        name = name.substr(7);
    }
    else if (name.rfind("class.", 0) == 0)
    {
        name = name.substr(6);
    }
    return name;
}

std::string getDITypeString(DIType *ty)
{
    if (!ty)
    {
        return "void";
    }
    std::string res;
    switch (ty->getTag())
    {
    case dwarf::DW_TAG_member:
    {
        auto derived = dyn_cast<DIDerivedType>(ty);
        res = "member: " + getDITypeString(derived->getBaseType());
        break;
    }
    case dwarf::DW_TAG_base_type:
    {
        res = ty->getName().str();
        break;
    }
    case dwarf::DW_TAG_volatile_type:
    case dwarf::DW_TAG_rvalue_reference_type:
    {
        auto derived = dyn_cast<DIDerivedType>(ty);
        res = getDITypeString(derived->getBaseType());
        break;
    }
    case dwarf::DW_TAG_typedef:
    {
        auto derived = dyn_cast<DIDerivedType>(ty);
        res = "typedef " + derived->getName().str() + "(" + getDITypeString(derived->getBaseType()) + ")";
        break;
    }
    case dwarf::DW_TAG_const_type:
    {
        auto derived = dyn_cast<DIDerivedType>(ty);
        res = "const " + getDITypeString(derived->getBaseType());
        break;
    }
    case dwarf::DW_TAG_pointer_type:
    {
        auto derived = dyn_cast<DIDerivedType>(ty);
        res = "*" + getDITypeString(derived->getBaseType());
        break;
    }
    case dwarf::DW_TAG_array_type:
    {
        auto derived = dyn_cast<DICompositeType>(ty);
        res = getDITypeString(derived->getBaseType()) + res;
        auto elements = derived->getElements();
        for (auto element : elements)
        {
            if (element->getTag() == dwarf::DW_TAG_subrange_type)
            {
                auto subrange = dyn_cast<DISubrange>(element);
                auto *CI = dyn_cast<ConstantInt *>(subrange->getCount());
                res += "[" + std::to_string(CI->getZExtValue()) + "]";
            }
        }

        break;
    }
    case dwarf::DW_TAG_class_type:
    case dwarf::DW_TAG_structure_type:
    {
        auto derived = dyn_cast<DICompositeType>(ty);
        res = derived->getName().str();
        if (res.empty())
        {
            res = "[unnamed]";
        }
        break;
    }
    case dwarf::DW_TAG_reference_type:
    {
        auto derived = dyn_cast<DIDerivedType>(ty);
        res = "ref " + getDITypeString(derived->getBaseType());
        break;
    }
    case dwarf::DW_TAG_union_type:
    {
        auto derived = dyn_cast<DICompositeType>(ty);
        res = "union.{";
        for (auto elem : derived->getElements())
        {
            res += getDITypeString(dyn_cast<DIType>(elem)) + ",";
        }
        res += "}";
        break;
    }
    default:
        res += std::to_string(ty->getTag());
        break;
    }
    return "(" + res + ")";
}

DIType *trimDerivedDIType(DIType *ty, llvm::dwarf::Tag till)
{
    while (ty)
    {
        if (auto *DITy = dyn_cast<DIDerivedType>(ty))
        {
            if (DITy->getTag() == till)
            {
                return DITy;
            }
            ty = DITy->getBaseType();
        }
        else
        {
            break;
        }
    }
    return ty;
}

DIType *pruneTypedef(DIType *ty)
{
    while (ty)
    {
        if (auto *DITy = dyn_cast<DIDerivedType>(ty))
        {
            if (DITy->getTag() == dwarf::DW_TAG_typedef || DITy->getTag() == dwarf::DW_TAG_const_type || DITy->getTag() == dwarf::DW_TAG_member || DITy->getTag() == dwarf::DW_TAG_volatile_type || DITy->getTag() == dwarf::DW_TAG_rvalue_reference_type || DITy->getTag() == dwarf::DW_TAG_inheritance)
            {
                ty = DITy->getBaseType();
            }
            else
            {
                break;
            }
        }
        else if (auto *DIType = dyn_cast<DICompositeType>(ty))
        {
            if (DIType->getTag() == dwarf::DW_TAG_enumeration_type)
            {
                ty = DIType->getBaseType();
            }
            else
            {
                break;
            }
        }
        else
        {
            break;
        }
    }
    return ty;
}

bool primitiveTypeCompatible(Type *ty, DIType *diElem)
{
    diElem = pruneTypedef(diElem);
    if (ty->isPointerTy() && (diElem->getTag() == dwarf::DW_TAG_pointer_type || diElem->getTag() == dwarf::DW_TAG_reference_type))
    {
        return true;
    }
    if (diElem->getTag() != dwarf::DW_TAG_base_type)
    {
        return false;
    }
    auto *basicType = dyn_cast<DIBasicType>(diElem);
    std::string basicTypeName = basicType->getName().str();
    if (basicTypeName.find("int") != std::string::npos || basicTypeName.find("long") != std::string::npos || basicTypeName.find("short") != std::string::npos || basicTypeName.find("char") != std::string::npos || basicTypeName.find("bool") != std::string::npos)
    {
        if (ty->isIntegerTy())
        {
            return basicType->getSizeInBits() == ty->getIntegerBitWidth();
        }
    }
    else if (basicTypeName.find("float") != std::string::npos)
    {
        if (ty->isFloatingPointTy())
        {
            return basicType->getSizeInBits() == ty->getPrimitiveSizeInBits();
        }
    }
    return false;
}

std::string pruneStructName(const std::string &structName)
{
    // if (structName.find("<") != string::npos)
    // {
    //     return structName.substr(0, structName.find("<"));
    // }
    // else if (structName.find(".") != string::npos)
    // {
    //     return structName.substr(0, structName.find("."));
    // }
    // else if (structName.find("::") != string::npos)
    // {
    //     string temp = structName.substr(structName.rfind("::") + 2);
    //     return pruneStructName(temp);
    // }
    // else
    // {
    //     return structName;
    // }
    ENV_DEBUG(errs() << "pruneStructName: " << structName << "\n");
    std::regex pattern(R"((?:class|struct|union)?\.?(?:.*?::)?([^:\.]+)(?:\.|$))");

    std::smatch matches;
    if (std::regex_search(structName, matches, pattern))
    {
        std::string temp = matches[1].str();
        ENV_DEBUG(errs() << "pruneStructName after regex: " << temp << "\n");
        if (temp.find("<") != std::string::npos)
        {
            return temp.substr(0, temp.find("<"));
        }
        else
        {
            return temp;
        }
    }

    return "";
}

int compositeTypeFieldCount(DICompositeType *CT)
{
    int count = 0;
    for (auto elem : CT->getElements())
    {
        if (elem->getTag() != dwarf::DW_TAG_subprogram)
        {
            count++;
        }
    }
    return count;
}

std::string DITypeName(DIType *ty)
{
    if (!ty->getName().empty())
    {
        return ty->getName().str();
    }
    return "DIType(" + ty->getFilename().str() + ":" + std::to_string(ty->getLine()) + ")";
}

std::string typeName(Type *ty)
{
    if (ty->isStructTy() && !ty->getStructName().str().empty())
    {
        return ty->getStructName().str();
    }
    std::string str;
    raw_string_ostream rso(str);
    ty->print(rso);
    return str;
}

std::string instructionValueName(Value *V)
{
    if (V->hasName())
    {
        return V->getName().str();
    }
    if (auto *inst = dyn_cast<Instruction>(V))
    {
        std::string str;
        raw_string_ostream rso(str);
        inst->print(rso);
        size_t pos = str.find('=');
        if (pos != std::string::npos)
        {
            str = str.substr(0, pos);
        }
        // Trim whitespace from both ends
        str.erase(0, str.find_first_not_of(" \t\n\r\f\v"));
        str.erase(str.find_last_not_of(" \t\n\r\f\v") + 1);
        return str;
    }
    else if (auto *Arg = dyn_cast<Argument>(V))
    {
        return Arg->getName().str();
    }
    return "";
}

Value *pruneBitfieldCasting(Value *V)
{
    while (V)
    {
        if (auto *inst = dyn_cast<Instruction>(V))
        {
            if (inst->getOpcode() == Instruction::ZExt || inst->getOpcode() == Instruction::Trunc)
            {
                V = *inst->user_begin();
            }
            else
            {
                return V;
            }
        }
        else
        {
            return V;
        }
    }
    return nullptr;
}

bool arrayDimensionContainsPointer(Type *ty)
{
    if (ty->isPointerTy())
    {
        return true;
    }
    if (!ty->isArrayTy())
    {
        return false;
    }
    return arrayDimensionContainsPointer(ty->getArrayElementType());
}

/**
 * 判断一个字符串是否是另一个字符串的前缀，并且除了前缀之后只有数字
 * @param prefix 前缀字符串
 * @param str 要检查的字符串
 * @return 如果满足条件返回true，否则返回false
 */
bool isPrefixWithOnlyDigits(const std::string &prefix, const std::string &str)
{
    // 首先检查是否是前缀
    if (str.compare(0, prefix.length(), prefix) != 0)
    {
        return false;
    }

    // 检查前缀之后的部分是否全是数字
    for (size_t i = prefix.length(); i < str.length(); ++i)
    {
        if (!isdigit(str[i]))
        {
            return false;
        }
    }

    return true;
}

VarInfoResolver::VarInfoResolver()
{
}

VarInfoResolver::~VarInfoResolver()
{
}

VarTypeInfo VarInfoResolver::resolveVarTypeFromDIType(DIType *type)
{
    if (!type)
    {
        VarTypeInfo info;
        info.kind = VarTypeInfo::Kind::Other;
        info.info.other.name = "void";
        return info;
    }

    ENV_DEBUG(dbgs() << "resolveVarTypeFromDIType: " << getDITypeString(type) << "\n");

    if (auto it = diTypeToVarTypeInfoCache.find(type); it != diTypeToVarTypeInfoCache.end())
    {
        ENV_DEBUG(dbgs() << "hit diTypeToVarTypeInfoCache: " << getDITypeString(type) << "\n");
        return it->second;
    }

    std::string typedefName;

    // 首先处理所有的 derived type，获取底层类型
    while (type)
    {
        if (auto derived = dyn_cast<DIDerivedType>(type))
        {
            if (derived->getTag() == llvm::dwarf::DW_TAG_typedef || derived->getTag() == llvm::dwarf::DW_TAG_const_type || derived->getTag() == llvm::dwarf::DW_TAG_volatile_type || derived->getTag() == llvm::dwarf::DW_TAG_rvalue_reference_type)
            {
                if (derived->getTag() == llvm::dwarf::DW_TAG_typedef && typedefName.empty())
                {
                    typedefName = derived->getName().str();
                }
                type = derived->getBaseType();
                continue;
            }
        }
        break;
    }

    if (!type)
    {
        VarTypeInfo info;
        info.kind = VarTypeInfo::Kind::Other;
        info.info.other.name = "void";
        return info;
    }

    if (auto *derived = dyn_cast<DIDerivedType>(type))
    {
        // 处理指针类型
        if (derived->getTag() == llvm::dwarf::DW_TAG_pointer_type || derived->getTag() == llvm::dwarf::DW_TAG_reference_type)
        {
            ENV_DEBUG(dbgs() << "DW_TAG_pointer_type: " << getDITypeString(derived) << "\n");
            VarTypeInfo info;
            info.typedef_name = typedefName;
            info.kind = VarTypeInfo::Kind::Pointer;
            info.info.pointer.pointee = std::make_unique<VarTypeInfo>(resolveVarTypeFromDIType(derived->getBaseType()));
            diTypeToVarTypeInfoCache[derived] = info;
            ENV_DEBUG(dbgs() << "resolved pointer var type: " << info.to_string() << ", DIType: " << getDITypeString(derived) << "\n");
            return info;
        }

        if (derived->getTag() == llvm::dwarf::DW_TAG_enumeration_type)
        {
            ENV_DEBUG(dbgs() << "DW_TAG_enumeration_type: " << getDITypeString(derived) << "\n");
            VarTypeInfo info;
            info.typedef_name = typedefName;
            info.kind = VarTypeInfo::Kind::Enum;
            info.info.enum_type.name = derived->getName().str();
            diTypeToVarTypeInfoCache[derived] = info;
            ENV_DEBUG(dbgs() << "resolved enum var type: " << info.to_string() << ", DIType: " << getDITypeString(derived) << "\n");
            return info;
        }

        if (derived->getTag() == llvm::dwarf::DW_TAG_member)
        {
            if (derived->isBitField())
            {
                ENV_DEBUG(dbgs() << "bitfield: " << derived->getName().str() << " " << derived->getOffsetInBits() << " " << derived->getSizeInBits() << "\n");
                // 处理位域
                VarTypeInfo info;
                info.typedef_name = typedefName;
                info.kind = VarTypeInfo::Kind::Bitfield;
                // 这里的 offset 是 bitfield 到 struct 头部的 offset
                info.info.bitfield.offset = derived->getOffsetInBits();
                info.info.bitfield.width = derived->getSizeInBits();
                diTypeToVarTypeInfoCache[derived] = info;
                return info;
            }
            else
            {
                ENV_DEBUG(dbgs() << "member: " << derived->getName().str() << "\n");
                // 普通成员变量
                VarTypeInfo info = resolveVarTypeFromDIType(derived->getBaseType());
                diTypeToVarTypeInfoCache[derived] = info;
                ENV_DEBUG(dbgs() << "resolved member var type: " << info.to_string() << ", DIType: " << getDITypeString(derived) << "\n");
                return info;
            }
        }
    }

    // 处理基本类型
    if (auto *basic = dyn_cast<DIBasicType>(type))
    {
        VarTypeInfo info;
        if (basic->getEncoding() == llvm::dwarf::DW_ATE_float)
        {
            info.kind = VarTypeInfo::Kind::Float;
        }
        else
        {
            info.kind = VarTypeInfo::Kind::Int;
        }
        info.typedef_name = typedefName;

        info.info.bits = basic->getSizeInBits();
        diTypeToVarTypeInfoCache[basic] = info;
        return info;
    }

    // 处理复合类型
    if (auto *composite = dyn_cast<DICompositeType>(type))
    {
        // 处理数组
        if (composite->getTag() == llvm::dwarf::DW_TAG_array_type)
        {
            ENV_DEBUG(dbgs() << "DW_TAG_array_type: " << getDITypeString(composite) << "\n");
            VarTypeInfo info;
            info.typedef_name = typedefName;
            info.kind = VarTypeInfo::Kind::Array;
            auto elemDIType = composite->getBaseType();
            auto prunedElemDIType = pruneTypedef(elemDIType);
            auto elemType = resolveVarTypeFromDIType(prunedElemDIType);
            ENV_DEBUG(dbgs() << "resolved array elem var type: " << elemType.to_string() << ", DIType: " << getDITypeString(prunedElemDIType) << "\n");
            auto elements = composite->getElements();
            if (!elements.empty())
            {
                VarTypeInfo *current = &info;
                for (int i = 0; i < elements.size(); i++)
                {
                    auto *element = elements[i];
                    if (auto *subrange = dyn_cast<DISubrange>(element))
                    {
                        if (auto *CI = dyn_cast<ConstantInt *>(subrange->getCount()))
                        {
                            current->info.array.length = CI->getZExtValue();
                        }

                        // Prepare for next dimension
                        if (i + 1 < elements.size())
                        {
                            current->info.array.elem_type = std::make_unique<VarTypeInfo>();
                            current->info.array.elem_type->kind = VarTypeInfo::Kind::Array;
                            current = current->info.array.elem_type.get();
                        }
                        else
                        {
                            // last dimension
                            current->info.array.elem_type = std::make_unique<VarTypeInfo>(elemType);
                        }
                    }
                }
            }
            diTypeToVarTypeInfoCache[composite] = info;
            ENV_DEBUG(dbgs() << "resolved array var type: " << info.to_string() << ", DIType: " << getDITypeString(composite) << "\n");
            return info;
        }

        // 处理结构体
        if (composite->getTag() == llvm::dwarf::DW_TAG_structure_type || composite->getTag() == llvm::dwarf::DW_TAG_class_type)
        {
            VarTypeInfo info;
            info.typedef_name = typedefName;
            info.kind = VarTypeInfo::Kind::Struct;
            info.info.struct_type.name = composite->getName().str();
            diTypeToVarTypeInfoCache[composite] = info;
            ENV_DEBUG(dbgs() << "resolved struct var type: " << info.to_string() << ", DIType: " << getDITypeString(composite) << "\n");
            return info;
        }

        if (composite->getTag() == llvm::dwarf::DW_TAG_enumeration_type)
        {
            VarTypeInfo info;
            info.typedef_name = typedefName;
            info.kind = VarTypeInfo::Kind::Enum;
            info.info.enum_type.name = composite->getName().str();
            diTypeToVarTypeInfoCache[composite] = info;
            ENV_DEBUG(dbgs() << "resolved enum var type: " << info.to_string() << ", DIType: " << getDITypeString(composite) << "\n");
            return info;
        }
    }

    // 其他类型
    VarTypeInfo info;
    info.typedef_name = typedefName;
    info.kind = VarTypeInfo::Kind::Other;
    info.info.other.name = type->getName().str().empty() ? "[unnamed]" : type->getName().str();
    diTypeToVarTypeInfoCache[type] = info;

    return info;
}

VarTypeInfo VarInfoResolver::fromTypeAndDIType(Type *ty, DIType *diType)
{
    ENV_DEBUG(dbgs() << "fromType: " << *ty << ", DIType: " << getDITypeString(diType) << "\n");
    if (!ty)
    {
        ENV_DEBUG(dbgs() << "fromType: nullptr\n");
        return VarTypeInfo();
    }

    assert(!ty->isPointerTy() || diType);
    if (ty->isPointerTy())
    {
        return resolveVarTypeFromDIType(diType);
    }

    VarTypeInfo info;

    if (ty->isFloatingPointTy())
    {
        info.kind = VarTypeInfo::Kind::Float;
        info.info.bits = ty->getScalarSizeInBits();
    }
    else if (ty->isIntegerTy())
    {
        info.kind = VarTypeInfo::Kind::Int;
        info.info.bits = ty->getIntegerBitWidth();
    }
    else if (ty->isStructTy())
    {
        info.kind = VarTypeInfo::Kind::Struct;
        info.info.struct_type.name = pruneStructName(ty->getStructName().str());
    }
    else if (ty->isArrayTy())
    {
        info.kind = VarTypeInfo::Kind::Array;
        info.info.array.length = ty->getArrayNumElements();
        info.info.array.elem_type = std::make_unique<VarTypeInfo>();
        if (ty->getArrayElementType()->isPointerTy())
        {
            info.info.array.elem_type->kind = VarTypeInfo::Kind::Pointer;
        }
        else if (ty->getArrayElementType()->isStructTy())
        {
            DIType *elementDIType = nullptr;
            if (auto *CT = dyn_cast<DICompositeType>(diType))
            {
                elementDIType = CT->getBaseType();
            }
            else
            {
                elementDIType = diType;
            }
            DIType *prunedDIType = pruneTypedef(elementDIType);
            auto elementTypeInfo = fromTypeAndDIType(ty->getArrayElementType(), prunedDIType);
            info.info.array.elem_type = std::make_unique<VarTypeInfo>(elementTypeInfo);
        }
        else
        {
            auto elementTypeInfo = fromTypeAndDIType(ty->getArrayElementType());
            info.info.array.elem_type = std::make_unique<VarTypeInfo>(elementTypeInfo);
        }
    }
    else if (ty->isVoidTy())
    {
        info.kind = VarTypeInfo::Kind::Other;
        info.info.other.name = "void";
    }
    else
    {
        ENV_DEBUG(dbgs() << "fromType: unknown type: " << *ty << "\n");
        info.kind = VarTypeInfo::Kind::Other;
        info.info.other.name = "unknown";
    }

    return info;
}

std::optional<VarInfo> VarInfoResolver::interpret(Module *M, Type *type, VarInfo var)
{
    // type can only be primitive type or vector type (<2 x i32>)
    assert(!type->isStructTy() && "type must not be a struct type");
    assert(!type->isArrayTy() && "type must not be an array type");

    if (type->isPointerTy())
    {
        return var;
    }

    if (!var.DIType)
    {
        return var;
    }

    ENV_DEBUG(errs() << "interpret: " << *type << ", DIType: " << getDITypeString(var.DIType) << ", var: " << var.type.to_string() << "\n");

    if (type->isVectorTy())
    {
        return std::nullopt;
    }

    DIType *addressDIType = var.DIType;
    addressDIType = pruneTypedef(addressDIType);
    if (primitiveTypeCompatible(type, addressDIType))
    {
        ENV_DEBUG(errs() << "interpret primitiveTypeCompatible: " << *type << ", " << getDITypeString(addressDIType) << "\n");
        return var;
    }
    if (auto *derived = dyn_cast<DIDerivedType>(addressDIType))
    {
        if (derived->getTag() == dwarf::DW_TAG_pointer_type)
        {
            addressDIType = derived->getBaseType();
            if (!pruneTypedef(addressDIType))
            {
                ENV_DEBUG(errs() << "interpret void*: " << *type << ", " << getDITypeString(derived) << "\n");
                return var;
            }
            if (primitiveTypeCompatible(type, addressDIType))
            {
                ENV_DEBUG(errs() << "interpret pointee: " << *type << ", " << getDITypeString(addressDIType) << "\n");
                return var;
            }
        }
    }
    if (addressDIType->getTag() == dwarf::DW_TAG_structure_type || addressDIType->getTag() == dwarf::DW_TAG_class_type)
    {
        DIType *fieldDIType = nullptr;
        fieldDIType = resolveStructFieldDIType(M, type, addressDIType, 0);
        ENV_DEBUG(dbgs() << "interpret resolveStructFieldDIType: " << *type << ", " << getDITypeString(var.DIType) << "\n");
        if (!fieldDIType)
        {
            fieldDIType = findFirstOffsetDIType(dyn_cast<DICompositeType>(addressDIType), 0);
            ENV_DEBUG(dbgs() << "interpret findFirstOffsetDIType: " << *type << ", " << getDITypeString(var.DIType) << "\n");
        }
        if (!fieldDIType)
        {
            return std::nullopt;
        }
        VarInfo current = var;
        current.name = fieldDIType->getName().str();
        current.type = resolveVarTypeFromDIType(fieldDIType);
        current.parent = std::make_unique<VarInfo>(var);
        current.DIType = pruneTypedef(fieldDIType);
        if (auto operand = interpret(M, type, current))
        {
            return operand;
        }
    }
    else if (addressDIType->getTag() == dwarf::DW_TAG_array_type)
    {
        DIType *arrayElemDIType = dyn_cast<DICompositeType>(addressDIType)->getBaseType();
        ENV_DEBUG(errs() << "interpret arrayElemDIType: " << *type << ", " << getDITypeString(var.DIType) << "\n");
        VarInfo current = var;
        current.name = arrayElemDIType->getName().str();
        current.type = resolveVarTypeFromDIType(arrayElemDIType);
        current.parent = std::make_unique<VarInfo>(var);
        current.DIType = pruneTypedef(arrayElemDIType);
        if (auto operand = interpret(M, type, current))
        {
            return operand;
        }
    }
    return std::nullopt;
}

bool VarInfoResolver::typeCompatible(Module *M, Type *ty, DICompositeType *CT, int fieldIdx)
{
    if (!ty->isStructTy() && !ty->isArrayTy())
    {
        return false;
    }

    // string typeName;
    // if (ty->isStructTy())
    // {
    //     typeName = getStructName(ty->getStructName().str());
    // }
    // else
    // {
    //     typeName = getStructName(ty->getArrayElementType()->getStructName().str());
    // }

    CT = dyn_cast<DICompositeType>(pruneTypedef(CT));
    ENV_DEBUG(errs() << "typeCompatible: " << *ty << ", " << getDITypeString(CT) << ", fieldIdx: " << fieldIdx << "\n");
    if (ty->isStructTy() && (CT->getTag() == dwarf::DW_TAG_structure_type || CT->getTag() == dwarf::DW_TAG_class_type))
    {
        auto DITypeName = pruneStructName(CT->getName().str());
        auto typeName = pruneStructName(getStructName(ty->getStructName().str()));

        ENV_DEBUG(errs() << "typeCompatible structs: " << typeName << ", " << DITypeName << "\n");

        if (DITypeName == typeName)
        {
            ENV_DEBUG(errs() << "typeCompatible structs: true\n");
            return true;
        }
    }
    else if (ty->isArrayTy() && CT->getTag() == dwarf::DW_TAG_array_type)
    {
        DIType *diElem = pruneTypedef(CT->getBaseType());
        if (auto *DIC = dyn_cast<DICompositeType>(diElem))
        {
            if (typeCompatible(M, ty->getArrayElementType(), DIC))
            {
                return true;
            }
        }
        else if (primitiveTypeCompatible(ty->getArrayElementType(), diElem))
        {
            return true;
        }
        else
        {
            return false;
        }
    }
    else if (CT->getTag() == dwarf::DW_TAG_array_type || ty->isArrayTy())
    {
        return false;
    }

    int diElemIdx = 0;
    int structElemIdx = 0;
    int virtualFieldCount = 0;

    ENV_DEBUG(dbgs() << "typeCompatible: " << CT->getElements().size() << ", " << ty->getStructNumElements() << "\n");

    if (fieldIdx != -1)
    {
        if (fieldIdx >= CT->getElements().size())
        {
            return false;
        }
        if (auto resolvedFieldDIType = resolveStructFieldDIType(M, ty, CT, fieldIdx))
        {
            return true;
        }
        else
        {
            return false;
        }

        int cursor = 0;
        DIType *foundElemDIType = nullptr;
        for (int i = 0; i < CT->getElements().size(); i++)
        {
            auto elemDIType = CT->getElements()[i];
            if (auto derived = dyn_cast<DIDerivedType>(elemDIType))
            {
                if (derived->getFlags() & DIType::DIFlags::FlagVirtual)
                {
                    continue;
                }
                else if (i > 0)
                {
                    if (auto lastDerived = dyn_cast<DIDerivedType>(CT->getElements()[i - 1]))
                    {
                        if (derived->getOffsetInBits() == lastDerived->getOffsetInBits())
                        {
                            continue;
                        }
                    }
                }
            }
            else if (auto *subprogram = dyn_cast<DISubprogram>(elemDIType))
            {
                continue;
            }
            if (cursor++ == fieldIdx)
            {
                foundElemDIType = dyn_cast<DIType>(elemDIType);
                break;
            }
        }
        if (!foundElemDIType)
        {
            return false;
        }
        ENV_DEBUG(dbgs() << "DDD: " << getDITypeString(foundElemDIType) << "\n");
        auto elemDIDerivedType = dyn_cast<DIDerivedType>(foundElemDIType);
        if (!elemDIDerivedType)
        {
            return false;
        }
        int elemDITypeOffset = elemDIDerivedType->getOffsetInBits();
        DIType *prunedElemDIType = pruneTypedef(dyn_cast<DIType>(foundElemDIType));
        ENV_DEBUG(dbgs() << "elemDITypeOffset: " << elemDITypeOffset << "\n");
        DataLayout DL(M);
        const StructLayout *SL = DL.getStructLayout(dyn_cast<StructType>(ty));
        bool matching = false;
        bool compatible = false;
        for (int i = 0; i < ty->getStructNumElements(); i++)
        {
            ENV_DEBUG(dbgs() << "i: " << i << ", offset: " << SL->getElementOffsetInBits(i) << "\n");
            if (elemDITypeOffset == SL->getElementOffsetInBits(i))
            {
                matching = true;
                ENV_DEBUG(dbgs() << "offset matching: " << i << ", " << *ty->getStructElementType(i) << "\n");
                if (auto *structDIType = dyn_cast<DICompositeType>(prunedElemDIType))
                {
                    compatible = typeCompatible(M, ty->getStructElementType(i), structDIType);
                    ENV_DEBUG(dbgs() << "struct type compatible: " << compatible << "\n");
                }
                else
                {
                    compatible = primitiveTypeCompatible(ty->getStructElementType(i), prunedElemDIType);
                    ENV_DEBUG(dbgs() << "primitive type compatible: " << compatible << "\n");
                }
                continue;
            }
            else if (matching)
            {
                return compatible;
            }
        }
        return compatible;
    }

    while (diElemIdx < CT->getElements().size() || structElemIdx < ty->getStructNumElements())
    {
        auto elemDIType = diElemIdx < CT->getElements().size() ? (DIType *)CT->getElements()[diElemIdx] : nullptr;
        auto elemType = structElemIdx < ty->getStructNumElements() ? ty->getStructElementType(structElemIdx) : nullptr;

        ENV_DEBUG(errs() << "typeCompatible diElemIdx: " << diElemIdx << ", structElemIdx: " << structElemIdx << "\n");

        // If the index of DICompositeType elements is in the end.
        // Checking if there are fields left in the struct type.
        // Considering virtual fields and padding fields located at the end of the struct.
        if (diElemIdx == CT->getElements().size() && structElemIdx + virtualFieldCount + 1 < ty->getStructNumElements())
        {
            ENV_DEBUG(errs() << "typeCompatible fields left in struct: " << ty->getStructName().str() << "\n");
            return false;
        }
        else if (diElemIdx == CT->getElements().size())
        {
            Type *paddingType = nullptr;
            if (ty->getStructElementType(ty->getStructNumElements() - 1)->isArrayTy())
            {
                paddingType = ty->getStructElementType(ty->getStructNumElements() - 1);
                if (paddingType->getArrayElementType()->isIntegerTy() && paddingType->getArrayElementType()->getIntegerBitWidth() == 8)
                {
                    return true;
                }
            }
            // Last field is not a padding field.
            return false;
        }
        else if (structElemIdx == ty->getStructNumElements())
        {
            return true;
        }

        if (auto *subprogram = dyn_cast<DISubprogram>(elemDIType))
        {
            diElemIdx++;
            continue;
        }
        if (elemDIType->getTag() == dwarf::DW_TAG_inheritance && elemDIType->getFlags() & DIType::DIFlags::FlagVirtual)
        {
            virtualFieldCount++;
        }
        elemDIType = dyn_cast<DIDerivedType>(elemDIType)->getBaseType();
        if (elemDIType->getFlags() & DIType::DIFlags::FlagStaticMember)
        {
            diElemIdx++;
            continue;
        }
        DIType *prunedElemDIType = pruneTypedef(elemDIType);
        if (auto *structDIType = dyn_cast<DICompositeType>(prunedElemDIType))
        {
            if (typeCompatible(M, elemType, structDIType))
            {
                diElemIdx++;
                structElemIdx++;
                continue;
            }
        }
        if (auto *derived = dyn_cast<DIDerivedType>(elemDIType))
        {
            if (trimDerivedDIType(derived, dwarf::DW_TAG_pointer_type) || trimDerivedDIType(derived, dwarf::DW_TAG_reference_type))
            {
                if (elemType->isPointerTy())
                {
                    diElemIdx++;
                    structElemIdx++;
                    continue;
                }
            }
        }
        if (auto *basicType = dyn_cast<DIBasicType>(prunedElemDIType))
        {
            if (primitiveTypeCompatible(elemType, basicType))
            {
                diElemIdx++;
                structElemIdx++;
                continue;
            }
        }

        ENV_DEBUG(errs() << "typeCompatible found incompatible type: " << *elemType << " " << getDITypeString(elemDIType) << "\n");
        return false;
    }

    ENV_DEBUG(dbgs() << "typeCompatible: true\n");
    return true;
}

void collectDICompositeTypes(DIType *Type, std::set<DIType *> &visited, std::map<std::string, DIType *> &map)
{
    if (!Type || visited.count(Type))
        return;
    visited.insert(Type);

    if (auto *CT = dyn_cast<DICompositeType>(Type))
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
            if (auto *Member = dyn_cast<DIDerivedType>(Element))
            {
                collectDICompositeTypes(Member->getBaseType(), visited, map);
            }
        }
        if (CT->getTag() == dwarf::DW_TAG_array_type)
        {
            collectDICompositeTypes(CT->getBaseType(), visited, map);
        }
    }
    else if (auto *DT = dyn_cast<DIDerivedType>(Type))
    {
        collectDICompositeTypes(DT->getBaseType(), visited, map);
    }
}

/**
 * GEP [n x i32], ptr %1, i32 0, i32 1
 * while %1 DIType could be struct or array
 */
DIType *VarInfoResolver::resolveArrayFieldDIType(Module *M, Type *type, DIType *arrayDIType, int fieldIndex)
{
    if (!type->isArrayTy() && !type->isPointerTy())
    {
        return nullptr;
    }
    if (!arrayDIType)
    {
        return nullptr;
    }
    if (!dyn_cast<DICompositeType>(arrayDIType))
    {
        return nullptr;
    }
    if (type->isPointerTy())
    {
        return dyn_cast<DICompositeType>(arrayDIType)->getBaseType();
    }
    ENV_DEBUG(dbgs() << "resolveArrayFieldDIType: " << typeName(type) << ", " << DITypeName(arrayDIType) << ", " << fieldIndex << "\n");
    std::string mappingKey = typeName(type) + "-" + DITypeName(arrayDIType);
    if (structFieldDITypeMapping.find(mappingKey) != structFieldDITypeMapping.end())
    {
        if (fieldIndex < structFieldDITypeMapping[mappingKey].size())
        {
            return structFieldDITypeMapping[mappingKey][fieldIndex];
        }
        else
        {
            return nullptr;
        }
    }
    auto arrayElemType = type->getArrayElementType();
    if (arrayDIType->getTag() == dwarf::DW_TAG_array_type)
    {
        // %1 is array type
        auto arrayElemDIType = dyn_cast<DICompositeType>(arrayDIType)->getBaseType();
        arrayElemDIType = pruneTypedef(arrayElemDIType);
        if (auto CT = dyn_cast<DICompositeType>(arrayElemDIType))
        {
            // %1 is an array of a struct type
            // case 1: %1's element type is exactly the same as the struct type
            // case 2: %1's element type is not matched, but its first field may be matched
            if (typeCompatible(M, arrayElemType, CT))
            {
                return arrayElemDIType;
            }
            else
            {
                auto firstFieldDIType = findFirstOffsetDIType(CT, 0);
                if (firstFieldDIType)
                {
                    return resolveArrayFieldDIType(M, type, firstFieldDIType, fieldIndex);
                }
            }
        }
        else
        {
            // %1 is an array of a primitive type
            if (primitiveTypeCompatible(arrayElemType, arrayElemDIType))
            {
                return arrayElemDIType;
            }
        }
    }
    else if (arrayDIType->getTag() == dwarf::DW_TAG_structure_type || arrayDIType->getTag() == dwarf::DW_TAG_class_type)
    {
        // %1 is struct type, then its type is not matched, but its first field may be matched
        auto CT = dyn_cast<DICompositeType>(arrayDIType);
        DIType *firstFieldDIType = findFirstOffsetDIType(CT, 0);
        if (firstFieldDIType)
        {
            firstFieldDIType = pruneTypedef(firstFieldDIType);
            return resolveArrayFieldDIType(M, type, firstFieldDIType, fieldIndex);
        }
    }
    return nullptr;
}

/**
 * GEP %struct.S, ptr %s, i32 0, i32 1
 * while %s DIType could be struct or array
 */
DIType *VarInfoResolver::resolveStructFieldDIType(Module *M, Type *type, DIType *structDIType, int fieldIndex, std::string mappingKey)
{
    if (!structDIType)
    {
        return nullptr;
    }
    if (!dyn_cast<DICompositeType>(structDIType))
    {
        return nullptr;
    }
    if (!type->isStructTy() && !type->isPointerTy())
    {
        return nullptr;
    }
    ENV_DEBUG(dbgs() << "resolveStructFieldDIType: " << typeName(type) << ", " << DITypeName(structDIType) << ", " << fieldIndex << "\n");
    if (mappingKey.empty())
    {
        mappingKey = typeName(type) + "-" + DITypeName(structDIType);
    }
    // if (structFieldDITypeMapping.find(mappingKey) != structFieldDITypeMapping.end())
    // {
    //     if (structFieldDITypeMapping[mappingKey].find(fieldIndex) != structFieldDITypeMapping[mappingKey].end())
    //     {
    //         return structFieldDITypeMapping[mappingKey][fieldIndex];
    //     }
    // }
    if (structDIType->getTag() == dwarf::DW_TAG_array_type)
    {
        // structDIType is array type, but type is a struct type
        // try to find the fieldIndex-th element in the array's first element as a struct type
        auto arrayElemDIType = dyn_cast<DICompositeType>(structDIType)->getBaseType();
        arrayElemDIType = pruneTypedef(arrayElemDIType);
        return resolveStructFieldDIType(M, type, arrayElemDIType, fieldIndex);
    }
    if (type->isPointerTy())
    {
        auto elements = dyn_cast<DICompositeType>(structDIType)->getElements();
        int i = 0;
        for (; i < elements.size() && fieldIndex > 0; i++)
        {
            if (auto derived = dyn_cast<DIDerivedType>(elements[i]))
            {
                if (derived->getFlags() & DIType::DIFlags::FlagVirtual || derived->getName().find("_vptr$") == 0)
                {
                    continue;
                }
                if (i > 0)
                {
                    auto lastDerived = dyn_cast<DIDerivedType>(elements[i - 1]);
                    if (derived->getOffsetInBits() != lastDerived->getOffsetInBits())
                    {
                        fieldIndex--;
                    }
                }
                else
                {
                    fieldIndex--;
                }
            }
        }
        return dyn_cast<DIType>(dyn_cast<DICompositeType>(structDIType)->getElements()[i]);
    }
    // Construct the mapping
    DataLayout DL(M);
    const StructLayout *SL = DL.getStructLayout(dyn_cast<StructType>(type));
    int diElemIndex = 0;
    int layoutIndex = 0;
    auto elements = dyn_cast<DICompositeType>(structDIType)->getElements();
    if (elements.size() == 0)
    {
        DIType *defDIType = structDITypes[structDIType->getName().str()];
        if (defDIType && dyn_cast<DICompositeType>(defDIType)->getElements().size() > 0)
        {
            elements = dyn_cast<DICompositeType>(defDIType)->getElements();
        }
        else
        {
            dbgs() << "[!] sgfuzz-source-pass: cannot find full definition, only forward declaration for type: " << structDIType->getName().str() << "\n";
            return nullptr;
        }
    }
    std::map<int, DIType *> fieldDITypes;
    // match the fields defined in StructType object and DICompositeType
    // StructType may contain padding object, merge multiple bitfield into one field element
    std::vector<bool> isPadding;
    while (diElemIndex < elements.size() && layoutIndex < type->getStructNumElements())
    {
        uint64_t layoutOffset = SL->getElementOffset(layoutIndex);
        Type *fieldType = type->getStructElementType(layoutIndex);
        ENV_DEBUG(dbgs() << "Struct type element: " << layoutIndex << ": " << *fieldType << ", offset: " << layoutOffset * 8 << "\n");
        if (auto derived = dyn_cast<DIDerivedType>(elements[diElemIndex]))
        {
            ENV_DEBUG(dbgs() << "DICompositeType element: " << diElemIndex << ": " << getDITypeString(dyn_cast<DIType>(elements[diElemIndex])) << ", offset: " << derived->getOffsetInBits() << "\n");
            if (derived->getFlags() & llvm::DINode::DIFlags::FlagStaticMember)
            {
                diElemIndex++;
                continue;
            }
            if (derived->getTag() == llvm::dwarf::DW_TAG_member && derived->getOffsetInBits() == layoutOffset * 8)
            {
                fieldDITypes[fieldDITypes.size()] = derived;
                isPadding.push_back(false);
                diElemIndex++;
                layoutIndex++;
            }
            else if (derived->getTag() == llvm::dwarf::DW_TAG_inheritance)
            {
                DICompositeType *baseCT = dyn_cast<DICompositeType>(derived->getBaseType());
                if (derived->getFlags() & llvm::DINode::DIFlags::FlagVirtual || isEmptyClass(baseCT))
                {
                    // virtual inheritance
                    diElemIndex++;
                }
                else if (derived->getOffsetInBits() == layoutOffset * 8)
                {
                    fieldDITypes[fieldDITypes.size()] = derived;
                    isPadding.push_back(false);
                    diElemIndex++;
                    layoutIndex++;
                }
                else
                {
                    diElemIndex++;
                    ENV_DEBUG(dbgs() << "diElemIndex++: " << diElemIndex << "\n");
                }
            }
            else if (derived->getOffsetInBits() > layoutOffset * 8)
            {
                layoutIndex++;
                isPadding.push_back(true);
                ENV_DEBUG(dbgs() << "layoutIndex++: " << layoutIndex << "\n");
                fieldDITypes[fieldDITypes.size()] = nullptr;
            }
            else
            {
                diElemIndex++;
                ENV_DEBUG(dbgs() << "diElemIndex++: " << diElemIndex << "\n");
            }
        }
        else if (auto subprogram = dyn_cast<DISubprogram>(elements[diElemIndex]))
        {
            diElemIndex++;
        }
    }
    structFieldDITypeMapping[mappingKey] = fieldDITypes;
    ENV_DEBUG(dbgs() << "resolveStructFieldDIType fieldIndex: " << fieldIndex << ", fieldDITypes.size(): " << fieldDITypes.size() << "\n");
    if (structFieldDITypeMapping[mappingKey].find(fieldIndex) != structFieldDITypeMapping[mappingKey].end() && !isPadding[fieldIndex])
    {
        ENV_DEBUG(dbgs() << "resolveStructFieldDIType fieldDITypes[fieldIndex]: " << getDITypeString(fieldDITypes[fieldIndex]) << "\n");
        return fieldDITypes[fieldIndex];
    }
    else
    {
        // fieldIndex is out of the fieldDITypes, means the field given by fieldIndex is not found in the DICompositeType
        DIType *firstFieldDIType = findFirstOffsetDIType(dyn_cast<DICompositeType>(structDIType), 0);
        firstFieldDIType = pruneTypedef(firstFieldDIType);
        ENV_DEBUG(dbgs() << "resolveStructFieldDIType firstFieldDIType: " << getDITypeString(firstFieldDIType) << "\n");
        if (firstFieldDIType)
        {
            DIType *fieldDIType = resolveStructFieldDIType(M, type, firstFieldDIType, fieldIndex, mappingKey);
            if (fieldDIType)
            {
                ENV_DEBUG(dbgs() << "resolveStructFieldDIType fieldDIType: " << getDITypeString(fieldDIType) << "\n");
                structFieldDITypeMapping[mappingKey][fieldIndex] = fieldDIType;
                return fieldDIType;
            }
        }
        std::string typeName = pruneStructName(type->getStructName().str());
        if (!typeName.empty())
        {
            auto defDIType = structDITypes[typeName];
            if (defDIType)
            {
                DIType *fieldDIType = resolveStructFieldDIType(M, type, defDIType, fieldIndex, mappingKey);
                if (fieldDIType)
                {
                    structFieldDITypeMapping[mappingKey][fieldIndex] = fieldDIType;
                    return fieldDIType;
                }
            }
            else
            {
                dbgs() << "[!] sgfuzz-source-pass: cannot find full definition, only forward declaration for type: " << typeName << "\n";
            }
        }
        return nullptr;
    }
}

void VarInfoResolver::collectAllStructDITypes(Module &M)
{
    NamedMDNode *CUNode = M.getNamedMetadata("llvm.dbg.cu");
    assert(CUNode);

    std::vector<DIType *> DITypesStack;
    std::set<DIType *> visited;

    std::string typedefName;
    for (auto &F : M)
    {
        // if (F.getName() == "_ZN28DcmQueryRetrieveProcessTableD2Ev")
        // {
        //     ENV_DEBUG(dbgs() << "collectAllStructDITypes for function: " << F.getName() << "\n");
        // }
        if (F.isDeclaration())
        {
            continue;
        }
        if (auto *SP = F.getSubprogram())
        {
            if (auto *SPType = SP->getType())
            {
                for (auto DIType : SPType->getTypeArray())
                {
                    if (F.getName() == "_ZN28DcmQueryRetrieveProcessTableD2Ev")
                    {
                        ENV_DEBUG(dbgs() << "collectAllStructDITypes for function, collected: " << getDITypeString(DIType) << "\n");
                    }
                    DITypesStack.push_back(DIType);
                }
            }
        }
        for (auto &BB : F)
        {
            for (auto &I : BB)
            {
                if (auto *DI = dyn_cast<DbgDeclareInst>(&I))
                {
                    if (auto *AI = dyn_cast<AllocaInst>(DI->getAddress()))
                    {
                        DITypesStack.push_back(DI->getVariable()->getType());
                    }
                }
            }
        }
    }

    for (MDNode *Node : CUNode->operands())
    {
        DICompileUnit *CU = dyn_cast<DICompileUnit>(Node);
        if (!CU)
            continue;

        for (DIScope *DS : CU->getRetainedTypes())
        {
            if (auto *DT = dyn_cast<DIType>(DS))
            {
                DITypesStack.push_back(DT);
            }
        }
        for (auto *DT : CU->getEnumTypes())
        {
            DITypesStack.push_back(DT);
        }
        for (DIGlobalVariableExpression *DGVE : CU->getGlobalVariables())
        {
            if (auto *DT = dyn_cast<DIType>(DGVE->getVariable()->getType()))
            {
                DITypesStack.push_back(DT);
            }
        }
        for (auto *IE : CU->getImportedEntities())
        {
            if (auto *DT = dyn_cast<DIType>(IE->getEntity()))
            {
                DITypesStack.push_back(DT);
            }
            else if (auto *DISP = dyn_cast<DISubprogram>(IE->getEntity()))
            {
                for (auto *Ty : DISP->getType()->getTypeArray())
                {
                    DITypesStack.push_back(Ty);
                }
            }
            else if (auto *DIVar = dyn_cast<DIVariable>(IE->getEntity()))
            {
                DITypesStack.push_back(DIVar->getType());
            }
        }
    }

    while (DITypesStack.size() > 0)
    {
        auto *DT = DITypesStack.back();
        DITypesStack.pop_back();
        if (!DT)
        {
            continue;
        }
        if (visited.find(DT) != visited.end())
            continue;
        visited.insert(DT);

        if (auto *CT = dyn_cast<DICompositeType>(DT))
        {
            if (CT->isForwardDecl())
            {
                continue;
            }
            if (CT->getTag() == dwarf::DW_TAG_structure_type || CT->getTag() == dwarf::DW_TAG_class_type)
            {
                if (!typedefName.empty())
                {
                    structDITypes[typedefName] = CT;
                    ENV_DEBUG(dbgs() << "collectAllStructDITypes: assign typedef: " << typedefName << ", DIType: " << getDITypeString(CT) << "\n");
                    typedefName.clear();
                }
                if (!CT->getName().empty())
                {

                    structDITypes[CT->getName().str()] = CT;
                }
                for (auto *Element : CT->getElements())
                {
                    if (auto *Derived = dyn_cast<DIDerivedType>(Element))
                    {
                        DITypesStack.push_back(Derived->getBaseType());
                    }
                    else if (auto *SP = dyn_cast<DISubprogram>(Element))
                    {
                        for (auto *Ty : SP->getType()->getTypeArray())
                        {
                            DITypesStack.push_back(Ty);
                        }
                    }
                }
            }
            else if (CT->getTag() == dwarf::DW_TAG_array_type)
            {
                DITypesStack.push_back(CT->getBaseType());
            }
        }
        else if (auto *derived = dyn_cast<DIDerivedType>(DT))
        {
            if (derived->getTag() == dwarf::DW_TAG_typedef)
            {
                typedefName = derived->getName().str();
                ENV_DEBUG(dbgs() << "collectAllStructDITypes: found typedef: " << typedefName << ", DIType: " << getDITypeString(derived->getBaseType()) << "\n");
            }
            DITypesStack.push_back(derived->getBaseType());
        }
    }

    for (auto &[name, CT] : structDITypes)
    {
        ENV_DEBUG(dbgs() << "struct type: " << name << ", DIType: " << getDITypeString(CT) << "\n");
    }
}

void VarInfoResolver::initDIRetainedTypes(Module &M)
{
    NamedMDNode *CUNode = M.getNamedMetadata("llvm.dbg.cu");
    assert(CUNode);

    for (MDNode *Node : CUNode->operands())
    {
        DICompileUnit *CU = dyn_cast<DICompileUnit>(Node);
        if (!CU)
            continue;

        for (DIScope *DS : CU->getRetainedTypes())
        {
            DIType *DT = dyn_cast<DIType>(DS);
            if (!DT)
                continue;
            diTypeToVarTypeInfoCache[DT] = resolveVarTypeFromDIType(DT);
            if (auto ST = dyn_cast<DICompositeType>(DT))
            {
                if (structDITypes.find(ST->getName().str()) == structDITypes.end() || !ST->isForwardDecl())
                {
                    structDITypes[ST->getName().str()] = ST;
                }
            }
        }
    }
}

// 初始化时收集全局变量信息
void VarInfoResolver::initGlobalVars(Module &M)
{
    // 收集结构体类型信息
    std::set<DIType *> visited;
    for (const Function &F : M)
    {
        if (DISubprogram *SP = F.getSubprogram())
        {
            // 收集函数参数和局部变量的类型信息
            for (const auto &BB : F)
            {
                for (const auto &I : BB)
                {
                    if (const DbgDeclareInst *DDI = dyn_cast<DbgDeclareInst>(&I))
                    {
                        if (DILocalVariable *DIVar = DDI->getVariable())
                        {
                            collectDICompositeTypes(DIVar->getType(), visited, structDITypes);
                        }
                    }
                }
            }
        }
    }

    // 收集全局变量信息
    for (GlobalVariable &GV : M.globals())
    {
        if (auto *DGV = GV.getMetadata("dbg"))
        {
            if (auto *DVE = dyn_cast<DIGlobalVariableExpression>(DGV))
            {
                auto DG = DVE->getVariable();
                global_vars[&GV] = DG;
                ENV_DEBUG(ENV_DEBUG(dbgs() << "collecting global: " << DG->getName().str() << "\n"));
                collectDICompositeTypes(DG->getType(), visited, structDITypes);
            }
        }
    }

    initDIRetainedTypes(M);

    // Print collected struct types
    ENV_DEBUG(dbgs() << "Collected global variable struct types:\n");
    for (const auto &[name, type] : structDITypes)
    {
        ENV_DEBUG(dbgs() << "  " << name << ": " << getDITypeString(type) << "\n");
    }
}

std::optional<std::string> VarInfoResolver::tryResolveBitfieldName(Module &M, DICompositeType *CT, int gepIndex, int bitfieldOffset)
{
    ENV_DEBUG(dbgs() << "Try resolving bitfield name, gepIdx: " << gepIndex << ", bitfieldOffset: " << bitfieldOffset << "\n");
    auto name = CT->getName().str();
    StructType *structType = nullptr;
    for (StructType *ST : M.getIdentifiedStructTypes())
    {
        if (ST->getName() == "struct." + name)
        {
            structType = ST;
            break;
        }
    }
    if (!structType)
    {
        return std::nullopt;
    }
    DataLayout DL(&M);
    const StructLayout *SL = DL.getStructLayout(structType);
    auto layoutOffsetInBits = SL->getElementOffset(gepIndex) * 8 + bitfieldOffset;
    ENV_DEBUG(dbgs() << "Resolved layoutOffsetInBits (from the beginning of the struct): " << layoutOffsetInBits << "\n");
    auto fieldDITypes = CT->getElements();
    for (int i = 0; i < fieldDITypes.size(); i++)
    {
        // TODO:
        // DIType 中的 bitoffset 是否包含 padding？
        auto fieldDIType = dyn_cast<DIType>(fieldDITypes[i]);
        if (fieldDIType)
        {
            ENV_DEBUG(dbgs() << "Resolving bitfield name from field DIType: " << fieldDIType->getName().str() << ", offset: " << fieldDIType->getOffsetInBits() << ", isBitField: " << (fieldDIType->isBitField() ? "true" : "false") << "\n");
        }
        if (fieldDIType && fieldDIType->getOffsetInBits() == layoutOffsetInBits)
        {
            if (fieldDIType->isBitField())
            {
                ENV_DEBUG(dbgs() << "Resolved bitfield name: " << fieldDIType->getName().str() << "\n");
                return fieldDIType->getName().str();
            }
            else
            {
                return std::nullopt;
            }
        }
    }

    return std::nullopt;
}

void VarInfoResolver::printStructLayout(Module &M, std::string name)
{
    if (!cachedEnv)
    {
        return;
    }
    StructType *structType = nullptr;
    for (StructType *ST : M.getIdentifiedStructTypes())
    {
        if (ST->getName() == "struct." + name || ST->getName() == "class." + name)
        {
            structType = ST;
            break;
        }
    }
    if (!structType)
    {
        return;
    }

    DataLayout DL(&M);
    const StructLayout *SL = DL.getStructLayout(structType);
    ENV_DEBUG(dbgs() << "struct field layout: " << name << "\n");
    for (unsigned i = 0; i < structType->getNumElements(); ++i)
    {
        auto field = structType->getElementType(i);
        auto offset = SL->getElementOffset(i);
        ENV_DEBUG(dbgs() << "field " << i << ": " << *field << ", offset: " << offset << "\n");
    }
}

DIType *VarInfoResolver::resolveStructField(Module &M, DICompositeType *CT, Type *type, std::vector<int> indices)
{
    if (!CT)
    {
        return nullptr;
    }
    if (!type->isStructTy())
    {
        return nullptr;
    }

    DIType *result = nullptr;

    ENV_DEBUG(ENV_DEBUG(dbgs() << "resolving struct field: " << CT->getName().str() << ", "));
    for (auto index : indices)
    {
        ENV_DEBUG(dbgs() << index << ", ");
    }
    ENV_DEBUG(dbgs() << "\n");

    std::vector<DIType *> fieldDITypes;

    for (auto index : indices)
    {
        ENV_DEBUG(dbgs() << "resolving struct field with one index: " << CT->getName().str() << ", " << index << "\n");
        fieldDITypes.clear();

        auto name = CT->getName().str();
        if (structFieldDITypeCache.find(CT) != structFieldDITypeCache.end())
        {
            // nullable
            if (index < structFieldDITypeCache[CT].size())
            {
                ENV_DEBUG(dbgs() << "hit struct field DIType cache: " << name << ", " << index << ", DIType: " << getDITypeString(structFieldDITypeCache[CT][index]) << "\n");
                result = structFieldDITypeCache[CT][index];
                if (auto *PCT = dyn_cast<DICompositeType>(pruneTypedef(result)))
                {
                    CT = PCT;
                    auto name = CT->getName().str();
                    type = type->getStructElementType(index);
                }
                continue;
            }
            else
            {
                ENV_DEBUG(dbgs() << "failed to resolve struct " << name << " field: " << index << ", index out of range\n");
                return nullptr;
            }
        }

        if (CT->getTag() == dwarf::DW_TAG_array_type)
        {
            ENV_DEBUG(dbgs() << "resolving struct field of array type: " << name << ", " << index << "\n");
            result = CT;
            if (auto *PCT = dyn_cast<DICompositeType>(pruneTypedef(CT->getBaseType())))
            {
                CT = PCT;
                type = type->getArrayElementType();
            }
            continue;
        }

        auto elements = CT->getElements();
        ENV_DEBUG(dbgs() << "elements size: " << elements.size() << "\n");

        if (elements.size() == 0)
        {
            DIType *DITypeDef = structDITypes[name];
            if (!DITypeDef || dyn_cast<DICompositeType>(DITypeDef)->isForwardDecl())
            {
                ENV_DEBUG(dbgs() << "failed to resolve struct " << name << " field: " << index << ", DICompositeType not found\n");
                return nullptr;
            }
            CT = dyn_cast<DICompositeType>(DITypeDef);
            if (!CT)
            {
                ENV_DEBUG(dbgs() << "failed to resolve struct " << name << " field: " << index << ", DICompositeType not found\n");
                return nullptr;
            }
            elements = CT->getElements();
        }

        DataLayout DL(&M);
        const StructLayout *SL = DL.getStructLayout(dyn_cast<StructType>(type));
        int diElemIndex = 0;
        int layoutIndex = 0;
        // match the fields defined in StructType object and DICompositeType
        // StructType may contain padding object, merge multiple bitfield into one field element
        while (diElemIndex < elements.size() && layoutIndex < type->getStructNumElements())
        {
            uint64_t layoutOffset = SL->getElementOffset(layoutIndex);
            ENV_DEBUG(dbgs() << "Struct type element: " << layoutIndex << ": " << *type->getStructElementType(layoutIndex) << ", offset: " << SL->getElementOffset(layoutIndex) * 8 << "\n");
            if (auto derived = dyn_cast<DIDerivedType>(elements[diElemIndex]))
            {
                ENV_DEBUG(dbgs() << "DICompositeType element: " << diElemIndex << ": " << getDITypeString(dyn_cast<DIType>(elements[diElemIndex])) << ", offset: " << derived->getOffsetInBits() << "\n");
                if (derived->isBitField() || (derived->getFlags() & llvm::DINode::DIFlags::FlagStaticMember))
                {
                    diElemIndex++;
                }
                else if (derived->getTag() == llvm::dwarf::DW_TAG_member && derived->getOffsetInBits() == layoutOffset * 8)
                {
                    fieldDITypes.push_back(derived);
                    diElemIndex++;
                    layoutIndex++;
                }
                else if (derived->getTag() == llvm::dwarf::DW_TAG_inheritance)
                {
                    DICompositeType *baseCT = dyn_cast<DICompositeType>(derived->getBaseType());
                    if (derived->getFlags() & llvm::DINode::DIFlags::FlagVirtual)
                    {
                        // virtual inheritance
                        diElemIndex++;
                    }
                    else if (derived->getOffsetInBits() == layoutOffset * 8 && typeCompatible(&M, type->getStructElementType(layoutIndex), baseCT, diElemIndex))
                    {
                        fieldDITypes.push_back(derived);
                        diElemIndex++;
                        layoutIndex++;
                    }
                    else
                    {
                        ENV_DEBUG(dbgs() << "diElemIndex++\n");
                        diElemIndex++;
                    }
                }
                else
                {
                    layoutIndex++;
                    fieldDITypes.push_back(nullptr);
                }
            }
            else if (auto subprogram = dyn_cast<DISubprogram>(elements[diElemIndex]))
            {
                ENV_DEBUG(dbgs() << "subprogram\n");
                diElemIndex++;
            }
        }

        // if (name == "ManualResetEvent")
        // {
        //     ENV_DEBUG(dbgs() << "debug ManualResetEvent\n");
        //     ENV_DEBUG(dbgs() << "fieldDITypes size: " << fieldDITypes.size() << "\n");
        //     for (auto field : fieldDITypes)
        //     {
        //         ENV_DEBUG(dbgs() << "field: " << getDITypeString(field) << "\n");
        //     }

        //     ENV_DEBUG(dbgs() << "type: " << *type << "\n");
        //     for (int i = 0; i < type->getStructNumElements(); i++)
        //     {
        //         ENV_DEBUG(dbgs() << "element " << i << ": " << *type->getStructElementType(i) << ", offset: " << SL->getElementOffset(i) << "\n");
        //     }
        // }

        if (!name.empty())
        {
            structFieldDITypeCache[CT] = fieldDITypes;
        }
        result = fieldDITypes[index];

        ENV_DEBUG(dbgs() << "resolveStructField: " << name << ", " << index << ", DIType: " << getDITypeString(fieldDITypes[index]) << "\n");

        if (auto *PCT = dyn_cast<DICompositeType>(pruneTypedef(result)))
        {
            CT = PCT;
            // for (StructType *ST : M.getIdentifiedStructTypes())
            // {
            //     if (ST->getName() == "struct." + name || ST->getName() == "class." + name)
            //     {
            //         ENV_DEBUG(dbgs() << "resolveStructField found struct type: " << name << ", DIType: " << getDITypeString(CT) << "\n");
            //         structType = ST;
            //         break;
            //     }
            // }
            type = type->getStructElementType(index);
        }
    }

    return result;
}

DIType *VarInfoResolver::resolveUnionFieldDIType(Module *M, Type *type, DIType *unionDIType, int fieldDIIndex)
{
    if (!type->isStructTy() && !type->isPointerTy())
    {
        return nullptr;
    }
    ENV_DEBUG(dbgs() << "resolveUnionFieldDIType: " << *type << ", " << getDITypeString(unionDIType) << ", fieldDIIndex: " << fieldDIIndex << "\n");
    if (auto CT = dyn_cast<DICompositeType>(unionDIType))
    {
        if (CT->getTag() == dwarf::DW_TAG_union_type)
        {
            return dyn_cast<DIType>(CT->getElements()[fieldDIIndex]);
        }
        else if (CT->getTag() == dwarf::DW_TAG_array_type)
        {
            auto baseType = CT->getBaseType();
            baseType = pruneTypedef(baseType);
            return resolveUnionFieldDIType(M, type, baseType, fieldDIIndex);
        }
        else
        {
            DIType *firstFieldDIType = findFirstOffsetDIType(CT, 0);
            firstFieldDIType = pruneTypedef(firstFieldDIType);
            if (firstFieldDIType)
            {
                return resolveUnionFieldDIType(M, type, firstFieldDIType, fieldDIIndex);
            }
        }
    }
    return nullptr;
}

DIType *VarInfoResolver::resolveUnionField(Module &M, DICompositeType *CT, GetElementPtrInst *GEP, std::vector<int> indices)
{
    auto gepFieldName = GEP->getName();

    // 对于 union，根据 user 的类型来判断 gep 取得的字段显然是不够的
    // 例如有的 union 中可能会有多个不同名称的 ptr
    // 或者 union 中包含 struct，而 struct 的第一个字段又是 ptr
    // 所以这里通过 gep value 的名称来辅助判断
    auto elements = CT->getElements();
    for (int i = 0; i < elements.size(); i++)
    {
        auto diField = elements[i];
        if (auto *derived = dyn_cast<DIDerivedType>(diField))
        {
            if (derived->getTag() == dwarf::DW_TAG_member)
            {
                if (isPrefixWithOnlyDigits(derived->getName().str(), gepFieldName.str()))
                {
                    return derived;
                }
                else if (auto *CT = dyn_cast<DICompositeType>(derived->getBaseType()))
                {
                    // 对于绕过 struct name （或者 struct 为 unnamed），直接访问 struct field 的
                    if (CT->getTag() == dwarf::DW_TAG_structure_type)
                    {
                        auto firstFieldName = dyn_cast<DIDerivedType>(CT->getElements()[0])->getName().str();
                        if (isPrefixWithOnlyDigits(firstFieldName, gepFieldName.str()))
                        {
                            return dyn_cast<DIDerivedType>(CT->getElements()[0]);
                        }
                        else if (indices.size() > 0)
                        {
                            return resolveStructField(M, CT, GEP->getSourceElementType(), indices);
                        }
                    }
                }
            }
        }
    }

    ENV_DEBUG(dbgs() << "failed to resolve union field: " << gepFieldName.str() << " in DI composite type: " << CT->getName().str() << "\n");
    return nullptr;
}

// 收集函数内的局部变量声明信息
void VarInfoResolver::collectFunctionLocalVars(Function &F)
{
    // ENV_DEBUG(dbgs() << "collectFunctionLocalVars: " << F.getName() << "\n");
    if (function_local_vars.find(&F) != function_local_vars.end())
    {
        // ENV_DEBUG(dbgs() << "collectFunctionLocalVars: " << F.getName() << " already collected\n");
        return; // 已经收集过该函数的信息
    }

    std::map<Value *, DILocalVariable *> local_vars;

    for (BasicBlock &BB : F)
    {
        for (Instruction &I : BB)
        {
            if (auto *DI = dyn_cast<DbgDeclareInst>(&I))
            {
                if (auto *AI = dyn_cast<AllocaInst>(DI->getAddress()))
                {
                    ENV_DEBUG(dbgs() << "collectFunctionLocalVars via DbgDeclareInst: " << instructionValueName(AI) << "\n");
                    local_vars[AI] = DI->getVariable();
                }
            }
            else if (auto *AI = dyn_cast<DbgAssignIntrinsic>(&I))
            {
                if (auto *V = AI->getAddress())
                {
                    ENV_DEBUG(dbgs() << "collectFunctionLocalVars via DbgAssignIntrinsic: " << instructionValueName(V) << "\n");
                    local_vars[V] = AI->getVariable();
                }
            }
            else if (auto *VI = dyn_cast<DbgValueInst>(&I))
            {
                // 对于 llvm.dbg.value 和 llvm.dbg.assign 指令
                if (auto *V = VI->getValue())
                {
                    ENV_DEBUG(dbgs() << "collectFunctionLocalVars via DbgValueInst: " << instructionValueName(V) << "\n");
                    local_vars[V] = VI->getVariable();
                }
            }
        }
    }

    function_local_vars[&F] = local_vars;
}

// 添加收集函数参数信息的方法
void VarInfoResolver::collectFunctionParams(Function &F)
{
    if (function_params.find(&F) != function_params.end())
    {
        return; // 已经收集过该函数的信息
    }

    std::map<Value *, VarInfo> params;
    if (DISubprogram *SP = F.getSubprogram())
    {
        if (auto *subRoutineType = dyn_cast<DISubroutineType>(SP->getType()))
        {
            if (F.getName() == "_ZL11readPDUBodyPP22PRIVATE_ASSOCIATIONKEY16DUL_BLOCKOPTIONSiPhmS3_S3_Pm")
            {
                ENV_DEBUG(dbgs() << "debug readPDUBody\n");
                ENV_DEBUG(dbgs() << "typearray size: " << subRoutineType->getTypeArray().size() << "\n");
                ENV_DEBUG(dbgs() << "F.arg_size(): " << F.arg_size() << "\n");
            }
            auto typeArray = subRoutineType->getTypeArray();
            int argOffset = typeArray.size() - F.arg_size();
            for (unsigned i = argOffset; i < typeArray.size() && (i - argOffset) < F.arg_size(); ++i)
            {
                if (auto *paramDIType = dyn_cast<DIType>(typeArray[i]))
                {
                    VarInfo info;
                    info.name = F.getArg(i - argOffset)->getName().str();
                    info.type = resolveVarTypeFromDIType(paramDIType);
                    info.is_param = true;
                    info.is_local = false;
                    info.is_global = false;
                    info.DIType = pruneTypedef(paramDIType);
                    if (auto *CT = dyn_cast<DICompositeType>(paramDIType))
                    {
                        std::set<DIType *> visited;
                        collectDICompositeTypes(CT, visited, structDITypes);
                    }
                    if (auto typedefName = resolveTypedefName(paramDIType))
                    {
                        ENV_DEBUG(dbgs() << "resolved param typedef: " << *typedefName << "\n");
                        info.type.typedef_name = *typedefName;
                    }
                    ENV_DEBUG(dbgs() << "collected param: " << info.name << " " << info.type.to_string() << "\n");
                    params[F.getArg(i - argOffset)] = info;
                }
            }
        }
    }
    function_params[&F] = params;
}

std::optional<VarInfo> VarInfoResolver::resolveBitfield(Function *F, Value *V, VarInfo *parentInfo)
{
    if (!parentInfo)
    {
        return std::nullopt;
    }
    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V);
    if (!GEP || GEP->getNumOperands() <= 2)
    {
        return std::nullopt;
    }
    auto prunedDIType = pruneTypedef(parentInfo->DIType);
    if (!prunedDIType)
    {
        return std::nullopt;
    }
    auto CT = dyn_cast<DICompositeType>(prunedDIType);
    if (!CT)
    {
        return std::nullopt;
    }
    auto CI = dyn_cast<ConstantInt>(GEP->getOperand(2));
    if (!CI)
    {
        return std::nullopt;
    }

    Instruction *bfLoad = nullptr;
    for (auto *user : GEP->users())
    {
        if (auto *load = dyn_cast<LoadInst>(user))
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

    VarInfo info = *parentInfo;
    VarTypeInfo bitfieldType;
    bitfieldType.kind = VarTypeInfo::Kind::Bitfield;

    info.parent = std::make_unique<VarInfo>(*parentInfo);
    info.type.kind = VarTypeInfo::Kind::Pointer;

    auto bfLoadUser = dyn_cast<Instruction>(*bfLoad->user_begin());
    if (bfLoadUser && bfLoadUser->getOpcode() == Instruction::And)
    {
        Instruction *andInst = bfLoadUser;
        auto andMsk = andInst->getOperand(1);
        if (auto *CI = dyn_cast<ConstantInt>(andMsk))
        {
            ENV_DEBUG(dbgs() << "Probe bfLoad: " << *bfLoad << "\n");
            ENV_DEBUG(dbgs() << "Probe andMsk: " << *andMsk << "\n");
            int trailingOnes = CI->getValue().countr_one();
            int consecutiveZeros = CI->getValue().getBitWidth() - CI->getValue().popcount();
            ENV_DEBUG(dbgs() << "trailingOnes: " << trailingOnes << ", consecutiveZeros: " << consecutiveZeros << "\n");
            bitfieldType.info.bitfield.offset = trailingOnes;
            bitfieldType.info.bitfield.width = consecutiveZeros;
        }
        else
        {
            return std::nullopt;
        }
    }
    else if (bfLoadUser && bfLoadUser->getOpcode() == Instruction::LShr)
    {
        Instruction *lshr = bfLoadUser;
        auto lshrOffset = lshr->getOperand(1);
        if (auto *CI = dyn_cast<ConstantInt>(lshrOffset))
        {
            ENV_DEBUG(dbgs() << "Probe LShr: " << *lshr << "\n");
            bitfieldType.info.bitfield.offset = CI->getZExtValue();
            auto lshrUser = pruneBitfieldCasting(*lshr->user_begin());
            if (!lshrUser)
            {
                ENV_DEBUG(dbgs() << "Unknown user of lshr when resolving bitfield width: " << *lshr << "\n");
                assert(false);
            }
            auto andInst = dyn_cast<Instruction>(lshrUser);
            if (andInst->getOpcode() == Instruction::And)
            {
                auto andMsk = andInst->getOperand(1);
                if (auto *CI = dyn_cast<ConstantInt>(andMsk))
                {
                    bitfieldType.info.bitfield.width = CI->getValue().popcount();
                }
            }
            else
            {
                // 没有 and 在 lshr 之后
                // 尝试简单推断，例如 i8 >> 7，那么 width 为 1
                bitfieldType.info.bitfield.width = dyn_cast<LoadInst>(bfLoad)->getType()->getIntegerBitWidth() - CI->getZExtValue();
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

    if (auto bfName = tryResolveBitfieldName(*F->getParent(), CT, CI->getZExtValue(), bitfieldType.info.bitfield.offset))
    {
        info.name = *bfName;
        info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(bitfieldType);
        ENV_DEBUG(dbgs() << info.type.to_string() << "\n");
        return info;
    }

    return std::nullopt;
}

// 解析变量信息的主函数
std::optional<VarInfo> VarInfoResolver::resolveVarInfo(Value *V, Function *F)
{
    ENV_DEBUG(dbgs() << "resolveVarInfo: " << *V << "\n");
    if (auto it = instructionVarInfoCache.find(V); it != instructionVarInfoCache.end())
    {
        ENV_DEBUG(dbgs() << "resolving hit cache: " << it->second.name << " " << it->second.type.to_string() << "\n");
        return it->second;
    }

    VarInfo info;

    // 处理全局变量
    if (auto *GV = dyn_cast<GlobalVariable>(V))
    {
        if (auto it = global_vars.find(GV); it != global_vars.end())
        {
            DIGlobalVariable *DGV = it->second;
            info.name = DGV->getName().empty() ? "" : DGV->getName().str();
            info.type.kind = VarTypeInfo::Kind::Pointer;
            auto prunedDIType = pruneTypedef(DGV->getType());
            info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(resolveVarTypeFromDIType(prunedDIType));
            if (auto typedefName = resolveTypedefName(DGV->getType()))
            {
                ENV_DEBUG(dbgs() << "resolved global typedef: " << *typedefName << "\n");
                info.type.info.pointer.pointee->typedef_name = *typedefName;
            }
            info.is_global = true;
            info.is_local = false;
            info.is_param = false;
            info.DIType = prunedDIType;
            ENV_DEBUG(dbgs() << "resolved global: " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");
            instructionVarInfoCache[GV] = info;
            return info;
        }

        return std::nullopt;
    }

    // 处理局部变量
    collectFunctionLocalVars(*F);
    auto &local_vars = function_local_vars[F];
    if (auto it = local_vars.find(V); it != local_vars.end())
    {
        // %1 = alloca i32, align 4, then the type of %1 is i32*
        // %1 = alloca ptr, align 8, then the type of %1 is ptr to the DIType
        DILocalVariable *DIVar = it->second;
        info.name = DIVar->getName().str();
        if (auto *AI = dyn_cast<AllocaInst>(V))
        {
            info.type.kind = VarTypeInfo::Kind::Pointer;
            info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(resolveVarTypeFromDIType(DIVar->getType()));
            if (auto typedefName = resolveTypedefName(DIVar->getType()))
            {
                ENV_DEBUG(dbgs() << "resolved local typedef: " << *typedefName << "\n");
                info.type.info.pointer.pointee->typedef_name = *typedefName;
            }
        }
        else
        {
            info.type = resolveVarTypeFromDIType(DIVar->getType());
            if (auto typedefName = resolveTypedefName(DIVar->getType()))
            {
                ENV_DEBUG(dbgs() << "resolved local typedef: " << *typedefName << "\n");
                info.type.typedef_name = *typedefName;
            }
        }
        // info.type = resolveDITypeToVarType(DIVar->getType());
        info.is_local = true;
        info.is_param = false;
        info.is_global = false;
        info.DIType = pruneTypedef(DIVar->getType());
        ENV_DEBUG(dbgs() << "resolved local: " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");
        instructionVarInfoCache[V] = info;
        return info;
    }

    // 处理函数参数
    if (auto *Arg = dyn_cast<Argument>(V))
    {
        collectFunctionParams(*F);
        auto &params = function_params[F];
        if (auto it = params.find(Arg); it != params.end())
        {
            ENV_DEBUG(dbgs() << "resolved param: " << it->second.name << ": " << it->second.type.to_string() << ", DIType: " << getDITypeString(it->second.DIType) << "\n");
            instructionVarInfoCache[Arg] = it->second;
            return it->second;
        }
        return std::nullopt;
    }

    if (auto *AI = dyn_cast<AllocaInst>(V))
    {
        // 不是局部变量和参数，而是 Alloca，可能是没有名称的临时局部变量
        // test(abc).another(def)
        if (!AI->getAllocatedType()->isPointerTy())
        {
            info.name = "[unamed]";
            info.type = fromTypeAndDIType(AI->getAllocatedType());
            if (info.type.kind == VarTypeInfo::Kind::Struct)
            {
                DIType *structDIType = getStructDIType(info.type.info.struct_type.name);
                info.DIType = structDIType;
            }
            info.is_local = true;
            info.is_param = false;
            info.is_global = false;
            instructionVarInfoCache[V] = info;
            ENV_DEBUG(dbgs() << "resolved unnamed alloca: " << *AI << ", type: " << info.type.to_string() << "\n");
            return info;
        }
    }

    // ZEXT
    if (auto *ZEXT = dyn_cast<ZExtInst>(V))
    {
        return resolveVarInfo(ZEXT->getOperand(0), F);
    }

    // 处理 GEP 指令（用于访问结构体成员或数组元素）
    if (auto *GEP = dyn_cast<GetElementPtrInst>(V))
    {
        auto GEPSrcTy = GEP->getSourceElementType();

        // 递归解析父结构
        if (auto parentInfo = resolveVarInfo(GEP->getPointerOperand(), F))
        {
            ENV_DEBUG(dbgs() << "resolved parentInfo: " << parentInfo->name << ": " << parentInfo->type.to_string() << ", DIType: " << getDITypeString(parentInfo->DIType) << "\n");

            if (auto bitfieldInfo = resolveBitfield(F, GEP, &parentInfo.value()))
            {
                ENV_DEBUG(dbgs() << "resolved bitfield: " << bitfieldInfo->name << ": " << bitfieldInfo->type.to_string() << ", DIType: " << getDITypeString(bitfieldInfo->DIType) << "\n");
                instructionVarInfoCache[GEP] = *bitfieldInfo;
                return *bitfieldInfo;
            }

            if (GEP->getNumOperands() <= 2)
            {
                // array element access
                // like: %add.ptr = getelementptr i8, ptr %36, i64 %idx.ext
                // !or! %arrayidx = getelementptr ptr, ptr %9, i64 %idxprom
                // !or! %arrayidx237 = getelementptr %struct.ASNSetData, ptr %144, i64 %idxprom236
                info = *parentInfo;
                if (parentInfo->parent)
                {
                    info.parent = std::make_unique<VarInfo>(*parentInfo->parent);
                }
                instructionVarInfoCache[GEP] = info;
                ENV_DEBUG(dbgs() << "resolved member: " << instructionValueName(V) << " -> " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");
                return info;
            }
            else
            {
                std::vector<int> fieldIndices;
                DICompositeType *CT = nullptr;

                // GEP->getNumOperands() >= 3
                if (GEPSrcTy->isArrayTy())
                {
                    // like: %arrayidx53 = getelementptr [7 x i32], ptr %endIdx, i64 0, i64 %idxprom52
                    // value is a pointer to i32
                    // like: %arrayidx = getelementptr [4 x ptr], ptr %td, i64 0, i64 0
                    // value is a pointer to ptr
                    // like: %arrayidx = getelementptr [300 x i8], ptr %suites7, i64 0, i64 %idxprom
                    // value is a pointer to i8
                    // like: %arrayidx = getelementptr [4 x [32 x ptr]], ptr @tagString, i64 0, i64 %idxprom
                    // value is a pointer to [32 x ptr]
                    // like: %type59 = getelementptr inbounds [4 x %struct._ISO2022Charset], ptr %psenc, i64 0, i64 %idxprom, i32 2

                    for (int i = 3; i < GEP->getNumOperands(); i++)
                    {
                        if (auto *CI = dyn_cast<ConstantInt>(GEP->getOperand(i)))
                        {
                            fieldIndices.push_back(CI->getZExtValue());
                        }
                    }

                    info = *parentInfo;
                    info.type = VarTypeInfo();

                    // Anyway, the type of GEP is a pointer to some type
                    info.type.kind = VarTypeInfo::Kind::Pointer;
                    info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>();

                    DICompositeType *parentArrayDIType = nullptr;
                    if (auto *CT = dyn_cast<DICompositeType>(parentInfo->DIType))
                    {
                        if (CT->getTag() == dwarf::DW_TAG_array_type)
                        {
                            info.DIType = pruneTypedef(CT->getBaseType());
                        }
                        parentArrayDIType = CT;
                    }
                    else if (auto derived = dyn_cast<DIDerivedType>(parentInfo->DIType))
                    {
                        // parent DIType is a pointer to some type
                        if (derived->getTag() == dwarf::DW_TAG_pointer_type || derived->getTag() == dwarf::DW_TAG_reference_type)
                        {
                            if (auto *DICT = dyn_cast<DICompositeType>(pruneTypedef(derived->getBaseType())))
                            {
                                parentArrayDIType = DICT;
                            }
                        }
                    };

                    auto arrayElemDIType = resolveArrayFieldDIType(F->getParent(), GEPSrcTy, parentArrayDIType, 0);
                    if (arrayElemDIType)
                    {
                        auto prunedArrayElemDIType = pruneTypedef(arrayElemDIType);
                        VarTypeInfo arrayElemVarType = resolveVarTypeFromDIType(prunedArrayElemDIType);
                        if (auto typedefName = resolveTypedefName(arrayElemDIType))
                        {
                            ENV_DEBUG(dbgs() << "resolved parent array element typedef: " << *typedefName << "\n");
                            info.type.info.pointer.pointee->typedef_name = *typedefName;
                        }
                        info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(arrayElemVarType);
                        info.is_local = parentInfo->is_local;
                        info.is_param = parentInfo->is_param;
                        info.is_global = parentInfo->is_global;
                        info.DIType = prunedArrayElemDIType;
                    }
                    else
                    {
                        auto arrayElemType = GEPSrcTy->getArrayElementType();
                        info.name = "[unamed]";
                        info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(fromTypeAndDIType(arrayElemType, nullptr));
                        info.is_local = parentInfo->is_local;
                        info.is_param = parentInfo->is_param;
                        info.is_global = parentInfo->is_global;
                        info.DIType = nullptr;
                    }

                    info.DIType = pruneTypedef(arrayElemDIType);

                    if (parentInfo->parent)
                    {
                        info.parent = std::make_unique<VarInfo>(*parentInfo->parent);
                    }

                    instructionVarInfoCache[GEP] = info;
                    ENV_DEBUG(dbgs() << "resolved member: " << V->getName() << " -> " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");

                    if (fieldIndices.empty())
                    {
                        return info;
                    }
                    else
                    {
                        DIType *prunedElementDIType = pruneTypedef(arrayElemDIType);
                        if (auto *composite = dyn_cast<DICompositeType>(prunedElementDIType))
                        {
                            CT = composite;
                        }
                        else
                        {
                            assert(false);
                        }
                        GEPSrcTy = GEPSrcTy->getArrayElementType();
                    }
                }
                else
                {
                    info = *parentInfo;
                    info.type = VarTypeInfo();

                    // Anyway, the type of GEP is a pointer to some type
                    info.type.kind = VarTypeInfo::Kind::Pointer;
                    info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>();

                    for (int i = 2; i < GEP->getNumOperands(); i++)
                    {
                        if (auto *CI = dyn_cast<ConstantInt>(GEP->getOperand(i)))
                        {
                            fieldIndices.push_back(CI->getZExtValue());
                        }
                    }

                    if (!parentInfo->DIType)
                    {
                        info.name = "[unnamed]";
                        Type *fieldType = GEPSrcTy;
                        while (fieldIndices.size() > 0)
                        {
                            int fieldIndex = fieldIndices.front();
                            fieldType = fieldType->getStructElementType(fieldIndex);
                            fieldIndices.erase(fieldIndices.begin());
                        }
                        info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(fromTypeAndDIType(fieldType, nullptr));
                        info.DIType = nullptr;
                        info.is_local = parentInfo->is_local;
                        info.is_param = parentInfo->is_param;
                        info.is_global = parentInfo->is_global;
                        info.parent = std::make_unique<VarInfo>(*parentInfo);
                        instructionVarInfoCache[GEP] = info;
                        dbgs() << "[!] sgfuzz-source-pass: cannot find the DIType of the GEP: " << *V << ", producing unnamed var with type: " << info.type.to_string() << "\n";
                        return info;
                    }

                    // the struct name of GEP source type may be the wrong one.
                    // for example:
                    // struct.a = type { i32, i32 }
                    // struct.b = type { i32, i32 }
                    // a and b are compatible types.
                    // %1 = getelementptr inbounds %struct.a, struct.b* %0, i32 0, i32 0
                    DICompositeType *parentDIType = nullptr;
                    if (auto DICT = dyn_cast<DICompositeType>(parentInfo->DIType))
                    {
                        parentDIType = DICT;
                    }
                    else if (auto derived = dyn_cast<DIDerivedType>(parentInfo->DIType))
                    {
                        DIType *DIType = parentInfo->DIType;
                        while (auto *derived = dyn_cast<DIDerivedType>(DIType))
                        {
                            DIType = derived->getBaseType();
                        }
                        parentDIType = dyn_cast<DICompositeType>(DIType);
                    }
                    if (parentDIType->isForwardDecl())
                    {
                        DIType *defDIType = structDITypes[parentDIType->getName().str()];
                        if (!defDIType)
                        {
                            ENV_DEBUG(dbgs() << "producing unnamed var" << "\n");
                            info.name = "[unnamed]";
                            Type *fieldType = GEPSrcTy;
                            while (fieldIndices.size() > 0)
                            {
                                int fieldIndex = fieldIndices.front();
                                fieldType = fieldType->getStructElementType(fieldIndex);
                                fieldIndices.erase(fieldIndices.begin());
                            }
                            info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(fromTypeAndDIType(GEPSrcTy, nullptr));
                            info.DIType = nullptr;
                            info.is_local = parentInfo->is_local;
                            info.is_param = parentInfo->is_param;
                            info.is_global = parentInfo->is_global;
                            info.parent = std::make_unique<VarInfo>(*parentInfo);
                            instructionVarInfoCache[GEP] = info;
                            dbgs() << "[!] sgfuzz-source-pass: cannot find the definition of the DIType " << parentDIType->getName().str() << ", when resolving GEP: " << V->getName() << ", producing unnamed var with type: " << info.type.to_string() << "\n";
                            return info;
                        }
                        parentDIType = dyn_cast<DICompositeType>(defDIType);
                    }
                    Type *fieldType = GEPSrcTy;
                    DIType *structFieldDIType = parentDIType;
                    ENV_DEBUG(dbgs() << "fieldType: " << *fieldType << ", parentDIType: " << getDITypeString(parentDIType) << "\n");
                    // vector<tuple<Type *, DIType *, int>> fieldIndexStack;
                    while (fieldIndices.size() > 0)
                    {
                        ENV_DEBUG(dbgs() << "while (fieldIndices.size() > 0) resolving struct field, fieldType: " << *fieldType << ", structFieldDIType: " << getDITypeString(structFieldDIType) << ", fieldIndices.front(): " << fieldIndices.front() << "\n");
                        int fieldIndex = fieldIndices.front();
                        auto prunedFieldDIType = pruneTypedef(structFieldDIType);
                        if (prunedFieldDIType->getTag() == dwarf::DW_TAG_ptr_to_member_type)
                        {
                            dbgs() << "[!] sgfuzz-source-pass: error in accessing field from DW_TAG_ptr_to_member_type " << *V << "\n";
                            return std::nullopt;
                        }
                        auto prunedDICT = dyn_cast<DICompositeType>(prunedFieldDIType);
                        ENV_DEBUG(dbgs() << "fieldType: " << *fieldType << ", prunedDICT: " << getDITypeString(prunedDICT) << "\n");
                        if (prunedDICT->getTag() == dwarf::DW_TAG_union_type)
                        {
                            // structFieldDIType = resolveUnionField(*F->getParent(), prunedDICT, GEP, fieldIndices);
                            structFieldDIType = resolveUnionFieldDIType(F->getParent(), fieldType, prunedDICT, fieldIndex);
                        }
                        else if (prunedDICT->getTag() == dwarf::DW_TAG_array_type)
                        {
                            structFieldDIType = dyn_cast<DICompositeType>(prunedFieldDIType)->getBaseType();
                        }
                        else
                        {
                            structFieldDIType = resolveStructFieldDIType(F->getParent(), fieldType, prunedFieldDIType, fieldIndex);
                        }
                        if (fieldType->isStructTy())
                        {
                            fieldType = fieldType->getStructElementType(fieldIndex);
                        }
                        else if (fieldType->isArrayTy())
                        {
                            fieldType = fieldType->getArrayElementType();
                        }
                        else
                        {
                            dbgs() << "[x] sgfuzz-source-pass: fieldType is not struct or array: " << *fieldType << "\n";
                            assert(false);
                        }
                        fieldIndices.erase(fieldIndices.begin());
                    }

                    ENV_DEBUG(dbgs() << "structFieldDIType: " << getDITypeString(structFieldDIType) << "\n");

                    if (structFieldDIType)
                    {
                        info.name = structFieldDIType->getName().str();
                        // info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(fromTypeAndDIType(fieldType, structFieldDIType));
                        info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(resolveVarTypeFromDIType(structFieldDIType));
                        info.DIType = pruneTypedef(structFieldDIType);
                        info.is_local = parentInfo->is_local;
                        info.is_param = parentInfo->is_param;
                        info.is_global = parentInfo->is_global;
                        info.parent = std::make_unique<VarInfo>(*parentInfo);
                        if (auto typedefName = resolveTypedefName(structFieldDIType))
                        {
                            ENV_DEBUG(dbgs() << "resolved parent array element typedef: " << *typedefName << "\n");
                            info.type.info.pointer.pointee->typedef_name = *typedefName;
                        }
                        instructionVarInfoCache[GEP] = info;
                        ENV_DEBUG(dbgs() << "resolved member: " << V->getName() << " -> " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");
                        return info;
                    }
                    else
                    {
                        info.name = "[unnamed]";
                        info.type.info.pointer.pointee = std::make_unique<VarTypeInfo>(fromTypeAndDIType(fieldType, nullptr));
                        info.DIType = nullptr;
                        info.is_local = parentInfo->is_local;
                        info.is_param = parentInfo->is_param;
                        info.is_global = parentInfo->is_global;
                        info.parent = std::make_unique<VarInfo>(*parentInfo);
                        instructionVarInfoCache[GEP] = info;
                        ENV_DEBUG(dbgs() << "resolved member: " << V->getName() << " -> " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");
                        return info;
                    }
                }
            }
        }
        return std::nullopt;
    }

    // TODO:
    // 处理 %1 = load ptr, union 结构
    // 需要根据 %1 的使用方式判断 %1 是 union 的哪个 field
    if (auto *LI = dyn_cast<LoadInst>(V))
    {
        auto LITy = LI->getType();
        if (auto ptrInfo = resolveVarInfo(LI->getPointerOperand(), F))
        {
            ENV_DEBUG(dbgs() << "resolved load ptr: " << instructionValueName(LI->getPointerOperand()) << " -> " << ptrInfo->name << ": " << ptrInfo->type.to_string() << ", DIType: " << getDITypeString(ptrInfo->DIType) << "\n");
            info = *ptrInfo;
            DIType *diType = nullptr;
            if (auto derived = dyn_cast<DIDerivedType>(ptrInfo->DIType))
            {
                if (derived->getTag() == dwarf::DW_TAG_pointer_type || derived->getTag() == dwarf::DW_TAG_reference_type)
                {
                    diType = derived->getBaseType();
                }
                else
                {
                    diType = derived;
                }
            }
            else if (auto CT = dyn_cast<DICompositeType>(ptrInfo->DIType))
            {
                if (CT->getTag() == dwarf::DW_TAG_array_type)
                {
                    diType = CT->getBaseType();
                }
                else
                {
                    diType = CT;
                }
            }
            else
            {
                diType = ptrInfo->DIType;
            }
            if (!LITy->isPointerTy())
            {
                DIType *prunedDIType = pruneTypedef(diType);
                info.type = fromTypeAndDIType(LITy, prunedDIType);
            }
            else if (ptrInfo->type.kind == VarTypeInfo::Kind::Pointer)
            {
                if (ptrInfo->type.info.pointer.pointee->kind == VarTypeInfo::Kind::Struct)
                {
                    // Since LLVM cannot load a struct into a register
                    // load ptr, ptr %1, where %1 is the address to a struct object
                    // it must be loading the pointer which is the first field of the struct
                    DICompositeType *DICT = dyn_cast<DICompositeType>(pruneTypedef(diType));
                    if (DIDerivedType *firstZeroOffset = findFirstOffsetDIType(DICT, 0))
                    {
                        DIType *prunedFirstOffsetZero = pruneTypedef(firstZeroOffset);
                        if (prunedFirstOffsetZero->getTag() == dwarf::DW_TAG_pointer_type)
                        {
                            info.type = resolveVarTypeFromDIType(prunedFirstOffsetZero);
                            diType = prunedFirstOffsetZero;
                        }
                    }
                }
                else
                {
                    info.type = *ptrInfo->type.info.pointer.pointee;
                }
            }
            else
            {
                assert(false);
            }
            if (ptrInfo->parent)
            {
                info.parent = std::make_unique<VarInfo>(*ptrInfo->parent);
            }
            info.DIType = pruneTypedef(diType);
            if (auto typedefName = resolveTypedefName(diType))
            {
                if (info.type.kind == VarTypeInfo::Kind::Pointer)
                {
                    info.type.info.pointer.pointee->typedef_name = *typedefName;
                }
                else
                {
                    info.type.typedef_name = *typedefName;
                }
                ENV_DEBUG(dbgs() << "resolved load typedef: " << *typedefName << "\n");
            }
            instructionVarInfoCache[LI] = info;
            ENV_DEBUG(dbgs() << "resolved load: " << instructionValueName(V) << " -> " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");
            return info;
        }
        return std::nullopt;
    }

    if (auto *PHI = dyn_cast<PHINode>(V))
    {
        // 在 PHI 的多个 incoming value 中，选择最早定义，且在该 PHI 指令之前的 value
        // 如果所有 incoming value 都在该 PHI 之后定义，那么可能存在问题
        BasicBlock *BB = PHI->getParent();
        Value *selectedIncomingValue = nullptr;
        for (auto &FBB : *F)
        {
            int FBBIndex = PHI->getBasicBlockIndex(&FBB);
            if (FBBIndex != -1)
            {
                selectedIncomingValue = PHI->getIncomingValue(FBBIndex);
                break;
            }
            else if (BB == &FBB)
            {
                return std::nullopt;
            }
        }
        if (auto incomingValueInfo = resolveVarInfo(selectedIncomingValue, F))
        {
            info = *incomingValueInfo;
            instructionVarInfoCache[PHI] = info;
            ENV_DEBUG(dbgs() << "resolved phi: " << instructionValueName(V) << " -> " << info.name << ": " << info.type.to_string() << ", DIType: " << getDITypeString(info.DIType) << "\n");
            return info;
        }
    }

    return std::nullopt;
}

DIType *VarInfoResolver::getStructDIType(const std::string &structName)
{
    std::string name = structName;
    if (name.rfind("struct.", 0) == 0)
    {
        name = name.substr(7);
    }
    else if (name.rfind("class.", 0) == 0)
    {
        name = name.substr(6);
    }
    auto it = structDITypes.find(name);
    if (it != structDITypes.end())
    {
        ENV_DEBUG(dbgs() << "find struct DIType: " << name << ": " << it->second->getName().str() << "\n");
        return it->second;
    }
    else
    {
        ENV_DEBUG(dbgs() << "failed to find struct DIType: " << name << "\n");
        return nullptr;
    }
}