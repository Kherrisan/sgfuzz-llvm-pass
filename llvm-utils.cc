#include "llvm-utils.h"
#include "utils.h"

using namespace llvm;

const DIFile *getFileFromScope(const DIScope *Scope)
{
    while (Scope)
    {
        if (auto *File = dyn_cast<DIFile>(Scope))
        {
            return File;
        }
        else if (auto *Subprogram = dyn_cast<DISubprogram>(Scope))
        {
            return Subprogram->getFile();
        }
        else if (auto *LexBlock = dyn_cast<DILexicalBlock>(Scope))
        {
            Scope = LexBlock->getScope();
        }
        else
        {
            break;
        }
    }
    return nullptr;
}

std::string getLocation(const Instruction *I)
{
    if (!I)
    {
        return "";
    }

    if (auto dbg = I->getDebugLoc())
    {
        unsigned line = dbg.getLine();
        unsigned column = dbg.getCol();
        const DIFile *file = getFileFromScope(dyn_cast<DIScope>(dbg.getScope()));
        if (file)
        {
            return file->getFilename().str() + ":" + std::to_string(line) + ":" + std::to_string(column);
        }
    }
    return "";
}

std::string getDITypeString(llvm::DIType *ty)
{
    if (!ty)
    {
        return "void";
    }
    std::string res;
    switch (ty->getTag())
    {
    case llvm::dwarf::DW_TAG_member:
    {
        auto derived = llvm::dyn_cast<llvm::DIDerivedType>(ty);
        res = getDITypeString(derived->getBaseType());
        break;
    }
    case llvm::dwarf::DW_TAG_base_type:
    {
        res = ty->getName().str();
        break;
    }
    case llvm::dwarf::DW_TAG_volatile_type:
    case llvm::dwarf::DW_TAG_rvalue_reference_type:
    {
        auto derived = llvm::dyn_cast<llvm::DIDerivedType>(ty);
        res = getDITypeString(derived->getBaseType());
        break;
    }
    case llvm::dwarf::DW_TAG_typedef:
    {
        auto derived = llvm::dyn_cast<llvm::DIDerivedType>(ty);
        res = "typedef " + derived->getName().str() + "(" + getDITypeString(derived->getBaseType()) + ")";
        break;
    }
    case llvm::dwarf::DW_TAG_const_type:
    {
        auto derived = llvm::dyn_cast<llvm::DIDerivedType>(ty);
        res = "const " + getDITypeString(derived->getBaseType());
        break;
    }
    case llvm::dwarf::DW_TAG_pointer_type:
    {
        auto derived = llvm::dyn_cast<llvm::DIDerivedType>(ty);
        res = "*" + getDITypeString(derived->getBaseType());
        break;
    }
    case llvm::dwarf::DW_TAG_array_type:
    {
        auto derived = llvm::dyn_cast<llvm::DICompositeType>(ty);
        res = getDITypeString(derived->getBaseType()) + res;
        auto elements = derived->getElements();
        for (auto element : elements)
        {
            if (element->getTag() == llvm::dwarf::DW_TAG_subrange_type)
            {
                auto subrange = llvm::dyn_cast<llvm::DISubrange>(element);
                auto *CI = llvm::dyn_cast<llvm::ConstantInt *>(subrange->getCount());
                if (CI)
                {
                    res += "[" + std::to_string(CI->getZExtValue()) + "]";
                }
                else
                {
                    res += "[unknown]";
                }
            }
        }

        break;
    }
    case llvm::dwarf::DW_TAG_class_type:
    case llvm::dwarf::DW_TAG_structure_type:
    {
        auto derived = llvm::dyn_cast<llvm::DICompositeType>(ty);
        res = derived->getName().str();
        if (res.empty())
        {
            res = "[unnamed]";
        }
        break;
    }
    case llvm::dwarf::DW_TAG_reference_type:
    {
        auto derived = llvm::dyn_cast<llvm::DIDerivedType>(ty);
        res = "ref " + getDITypeString(derived->getBaseType());
        break;
    }
    case llvm::dwarf::DW_TAG_union_type:
    {
        auto derived = llvm::dyn_cast<llvm::DICompositeType>(ty);
        res = "union.{";
        for (auto elem : derived->getElements())
        {
            res += getDITypeString(llvm::dyn_cast<llvm::DIType>(elem)) + ",";
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

std::string canonicalizeTypedefDIType(llvm::DIType *&ty)
{
    std::string typedefName;
    while (ty)
    {
        if (auto *DITy = llvm::dyn_cast<llvm::DIDerivedType>(ty))
        {
            if (DITy->getTag() == llvm::dwarf::DW_TAG_typedef || DITy->getTag() == llvm::dwarf::DW_TAG_const_type || DITy->getTag() == llvm::dwarf::DW_TAG_member || DITy->getTag() == llvm::dwarf::DW_TAG_volatile_type || DITy->getTag() == llvm::dwarf::DW_TAG_rvalue_reference_type || DITy->getTag() == llvm::dwarf::DW_TAG_inheritance || DITy->getTag() == llvm::dwarf::DW_TAG_atomic_type)
            {
                if (DITy->getTag() == llvm::dwarf::DW_TAG_typedef)
                {
                    typedefName = DITy->getName().str();
                }
                ty = DITy->getBaseType();
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
    return typedefName;
}

std::string pruneStructName(const std::string &structName)
{
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

int getTypeSizeInBits(Module *M, Type *ty)
{
    if (ty->isPointerTy())
    {
        return 64;
    }
    else if (ty->isStructTy())
    {
        llvm::DataLayout DL(M);
        const llvm::StructLayout *SL = DL.getStructLayout(llvm::dyn_cast<llvm::StructType>(ty));
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

void printStructLayout(Module &M, std::string name)
{
    if (!ENV_LOG_ENABLED)
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