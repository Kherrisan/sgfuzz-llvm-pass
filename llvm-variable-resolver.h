#pragma once

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
#include "llvm-variable-type.h"

namespace pingu
{
    class VarInfo
    {
    public:
        std::string name;
        Type *type;
        bool is_local;
        bool is_param;
        bool is_global;
        std::shared_ptr<VarInfo> parent;

        // 拷贝构造函数
        VarInfo(const VarInfo &other)
            : name(other.name), type(other.type), is_local(other.is_local), is_param(other.is_param), is_global(other.is_global)
        {
            parent = other.parent ? std::make_shared<VarInfo>(*other.parent) : nullptr;
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
                parent = other.parent ? std::make_shared<VarInfo>(*other.parent) : nullptr;
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
                {"ty", type->toJson()},
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

        void collectDIRetainedTypes(llvm::Module &M);
        void collectGlobalVars(llvm::Module &M);
        void collectFunctionLocalVars(llvm::Function &F);
        void collectFunctionParams(llvm::Function &F);

        std::optional<Type *> resolveBitfield(llvm::GetElementPtrInst *GEP, VarInfo *parent);
        std::optional<VarInfo> resolveGEP(llvm::GetElementPtrInst *GEP);
        std::optional<VarInfo> resolveLoad(llvm::LoadInst *LI);
        std::optional<VarInfo> resolvePHI(llvm::PHINode *PN);

        std::optional<VarInfo> join(VarInfo &parent, std::vector<Member> &memberRefs);

        std::map<llvm::Value *, VarInfo> valueVarInfoCache;
    public:
        VarInfoResolver();
        ~VarInfoResolver();

        std::optional<VarInfo> interpret(llvm::Module *M, llvm::Type *type, VarInfo var);
        std::optional<VarInfo> resolveVarInfo(llvm::Value *V, llvm::Function *F);
        void collectDITypes(llvm::Module &M);
    };
}