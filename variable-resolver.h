#include "include/json.hpp"

#include <map>
#include <string>
#include <vector>
#include <llvm/IR/Value.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"

#include "utils.h"

using namespace llvm;

struct VarTypeInfo
{

    VarTypeInfo() {}

    enum class Kind
    {
        Int,
        Float,
        Pointer,
        Array,
        Struct,
        Bitfield,
        Enum,
        Other
    } kind;

    std::optional<std::string> typedef_name;

    // 类型特定的信息
    struct
    {
        uint16_t bits; // for Int/Float
        struct
        {
            uint16_t offset;
            uint16_t width;
        } bitfield;
        struct
        {
            std::unique_ptr<VarTypeInfo> elem_type;
            std::optional<size_t> length;
        } array;
        struct
        {
            std::unique_ptr<VarTypeInfo> pointee;
        } pointer;
        struct
        {
            std::string name;
        } struct_type;
        struct
        {
            std::string name;
        } other;
        struct
        {
            std::string name;
        } enum_type;
    } info;

    VarTypeInfo &operator=(const VarTypeInfo &other)
    {
        typedef_name = other.typedef_name;
        kind = other.kind;
        switch (kind)
        {
        case Kind::Int:
        case Kind::Float:
            info.bits = other.info.bits;
            break;
        case Kind::Pointer:
            info.pointer.pointee = other.info.pointer.pointee ? std::make_unique<VarTypeInfo>(*other.info.pointer.pointee) : nullptr;
            break;
        case Kind::Array:
            info.array.elem_type = other.info.array.elem_type ? std::make_unique<VarTypeInfo>(*other.info.array.elem_type) : nullptr;
            info.array.length = other.info.array.length;
            break;
        case Kind::Struct:
            info.struct_type.name = other.info.struct_type.name;
            break;
        case Kind::Bitfield:
            info.bitfield = other.info.bitfield;
            break;
        case Kind::Other:
            info.other.name = other.info.other.name;
            break;
        case Kind::Enum:
            info.enum_type.name = other.info.enum_type.name;
            break;
        }
        return *this;
    }

    VarTypeInfo(const VarTypeInfo &other)
    {
        typedef_name = other.typedef_name;
        kind = other.kind;
        switch (kind)
        {
        case Kind::Int:
        case Kind::Float:
            info.bits = other.info.bits;
            break;
        case Kind::Pointer:
            info.pointer.pointee = other.info.pointer.pointee ? std::make_unique<VarTypeInfo>(*other.info.pointer.pointee) : nullptr;
            break;
        case Kind::Array:
            info.array.elem_type = other.info.array.elem_type ? std::make_unique<VarTypeInfo>(*other.info.array.elem_type) : nullptr;
            info.array.length = other.info.array.length;
            break;
        case Kind::Struct:
            info.struct_type.name = other.info.struct_type.name;
            break;
        case Kind::Bitfield:
            info.bitfield = other.info.bitfield;
            break;
        case Kind::Other:
            info.other.name = other.info.other.name;
            break;
        case Kind::Enum:
            info.enum_type.name = other.info.enum_type.name;
            break;
        }
    }

    // JSON 序列化方法
    nlohmann::json to_json() const
    {
        nlohmann::json j;
        if (typedef_name)
        {
            // ENV_DEBUG(dbgs() << "Serialized typedef_name to json: " << *typedef_name << "\n");
            j["typedef_name"] = *typedef_name;
        }
        switch (kind)
        {
        case Kind::Int:
            j["Int"] = {{"bits", info.bits}};
            break;
        case Kind::Float:
            j["Float"] = {{"bits", info.bits}};
            break;
        case Kind::Pointer:
            j["Pointer"] = {{"pointee", info.pointer.pointee->to_json()}};
            break;
        case Kind::Array:
        {
            nlohmann::json array_info;
            array_info["elem_type"] = info.array.elem_type->to_json();
            if (info.array.length)
            {
                array_info["length"] = info.array.length.value();
            }
            j["Array"] = array_info;
            break;
        }
        case Kind::Struct:
            j["Struct"] = {{"name", info.struct_type.name}};
            break;
        case Kind::Bitfield:
            j["Bitfield"] = {{"offset", info.bitfield.offset}, {"width", info.bitfield.width}};
            break;
        case Kind::Other:
            j = {{"Other", {{"name", info.other.name}}}};
            break;
        case Kind::Enum:
            j["Enum"] = {{"name", info.enum_type.name}};
            break;
        }
        return j;
    }

    std::string to_string() const
    {
        std::string name;
        switch (kind)
        {
        case Kind::Int:
            name = "u" + std::to_string(info.bits);
            break;
        case Kind::Float:
            name = "f" + std::to_string(info.bits);
            break;
        case Kind::Pointer:
            name = "*" + (info.pointer.pointee ? info.pointer.pointee->to_string() : "unknown");
            break;
        case Kind::Array:
            name = (info.array.elem_type ? info.array.elem_type->to_string() : "unknown") +
                   "[" + (info.array.length ? std::to_string(info.array.length.value()) : "") + "]";
            break;
        case Kind::Struct:
            name = "struct." + info.struct_type.name;
            break;
        case Kind::Bitfield:
            name = "bitfield{width: " + std::to_string(info.bitfield.width) + ", offset: " + std::to_string(info.bitfield.offset) + "}";
            break;
        case Kind::Other:
            name = "other." + info.other.name;
            break;
        case Kind::Enum:
            name = "enum." + info.enum_type.name;
            break;
        default:
            name = "unknown";
        }
        if (typedef_name)
        {
            name = *typedef_name + "(" + name + ")";
        }
        return name;
    }
};

struct VarInfo
{
    std::string name;
    VarTypeInfo type;
    bool is_local;
    bool is_param;
    bool is_global;
    std::unique_ptr<VarInfo> parent;
    DIType *DIType;

    // 拷贝构造函数
    VarInfo(const VarInfo &other)
        : name(other.name), is_local(other.is_local), is_param(other.is_param), is_global(other.is_global), DIType(other.DIType)
    {
        type = other.type;
        parent = other.parent ? std::make_unique<VarInfo>(*other.parent) : nullptr;
    }

    // 赋值运算符
    VarInfo &operator=(const VarInfo &other)
    {
        if (this != &other)
        {
            name = other.name;
            type = other.type;
            is_local = other.is_local;
            is_param = other.is_param;
            is_global = other.is_global;
            DIType = other.DIType;
            parent = other.parent ? std::make_unique<VarInfo>(*other.parent) : nullptr;
        }
        return *this;
    }

    // 默认构造函数
    VarInfo() = default;

    nlohmann::json to_json() const
    {
        nlohmann::json j;
        j = {
            {"name", name},
            {"ty", type.to_json()},
            {"is_local", is_local},
            {"is_param", is_param},
            {"is_global", is_global}};
        if (parent)
        {
            j["parent"] = parent->to_json();
        }
        return j;
    }
};

class VarInfoResolver
{
private:
    // 缓存每个函数的局部变量声明信息
    std::map<Function *, std::map<Value *, DILocalVariable *>> function_local_vars;
    // 缓存全局变量信息
    std::map<GlobalVariable *, DIGlobalVariable *> global_vars;
    // 添加函数参数缓存
    std::map<Function *, std::map<Value *, VarInfo>> function_params;
    // LOAD 和 GEP 指令缓存
    std::map<Value *, VarInfo> instructionVarInfoCache;

    std::map<DIType *, VarTypeInfo> diTypeToVarTypeInfoCache;

    std::map<Value *, DIType *> valueDITypeCache;

    std::map<DIType *, std::vector<DIType *>> structFieldDITypeCache;

    std::map<DICompositeType *, std::vector<DIDerivedType *>> unionFieldDITypeCache;

    std::map<std::string, DIType *> structDITypes;

    std::map<std::string, std::map<int, DIType *>> structFieldDITypeMapping;

    VarTypeInfo resolveVarTypeFromDIType(DIType *type);
    VarTypeInfo fromTypeAndDIType(Type *ty, DIType *diType = nullptr);
    bool typeCompatible(Module *M, Type *ty, DICompositeType *CT, int fieldIdx = -1);
    DIType *resolveArrayFieldDIType(Module *M, Type *type, DIType *arrayDIType, int fieldIndex);
    DIType *resolveStructFieldDIType(Module *M, Type *type, DIType *structDIType, int fieldIndex, std::string mappingKey = "");
    void initDIRetainedTypes(Module &M);
    std::optional<std::string> tryResolveBitfieldName(Module &M, DICompositeType *CT, int gepIndex, int bitfieldOffset);
    void printStructLayout(Module &M, std::string name);
    DIType *resolveStructField(Module &M, DICompositeType *CT, Type *type, std::vector<int> indices);
    DIType *resolveUnionFieldDIType(Module *M, Type *type, DIType *unionDIType, int fieldDIIndex);
    DIType *resolveUnionField(Module &M, DICompositeType *CT, GetElementPtrInst *GEP, std::vector<int> indices);
    void collectFunctionParams(Function &F);
    std::optional<VarInfo> resolveBitfield(Function *F, Value *V, VarInfo *parentInfo);
    DIType *getStructDIType(const std::string &structName);

public:
    VarInfoResolver();
    ~VarInfoResolver();

    void initGlobalVars(Module &M);
    std::optional<VarInfo> interpret(Module *M, Type *type, VarInfo var);
    std::optional<VarInfo> resolveVarInfo(Value *V, Function *F);
    void collectAllStructDITypes(Module &M);
    void collectFunctionLocalVars(Function &F);
};