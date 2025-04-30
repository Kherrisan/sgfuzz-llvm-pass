#pragma once

#include "include/json.hpp"

#include <llvm/IR/Value.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/BinaryFormat/Dwarf.h>

#include "llvm-utils.h"

#define ARRAY_INDEXED_NAME "###ARRAY_INDEXED_NAME###"

namespace pingu
{
    class Type;
    class IndexedType;
    class Int;
    class Float;
    class Pointer;
    class Array;
    class Struct;
    class Union;
    class Bitfield;
    class Enum;
    class Other;

    typedef std::tuple<std::string, Type *> Member;

    class Type
    {
    protected:
        std::string m_typedefName;
        int m_size;

    public:
        enum class Kind
        {
            Void,
            Int,
            Float,
            Pointer,
            Array,
            Struct,
            Union,
            Bitfield,
            Enum,
            Other,
        };

        static Type *fromName(std::string name);
        static Type *fromType(llvm::Module *module, llvm::Type *llvmType);
        static Type *fromDIType(llvm::DIType *diType);
        static Type *fromTypeID(Type *type);
        static std::vector<Type *> &declareTypes();
        static bool isFromType(Type *type);
        static bool isFromDIType(Type *type);

        virtual Type *interpreteAs(Type *other, std::vector<Member> &memberRefs, std::string &loadValueName);
        virtual nlohmann::json toJson() const = 0;
        virtual std::string toString() const = 0;
        virtual nlohmann::json toDebugJson() const;
        virtual bool isIndexable() const;
        std::string name() const;

        virtual bool isDeclaration() const;
        std::string typedefName() const;
        virtual int size();
        virtual std::string id() const;
        virtual Kind kind() const = 0;

        friend std::ostream &operator<<(std::ostream &os, const Type &type);

        Type();
        Type(const Type &other);
        virtual ~Type() {}

    protected:
    private:
        static std::map<llvm::DIType *, Type *> m_diTypeCache;
        static std::map<llvm::Type *, Type *> m_typeCache;
        static std::map<std::string, Type *> m_idCache;
        static std::map<std::string, Type *> m_namedStructCache;
        static std::vector<llvm::DIType *> m_diTypeParsingStack;
        static std::vector<Type *> m_declarationTypes;
    };

    class IndexedType : public Type
    {
    public:
        IndexedType(int count, int size);
        IndexedType(const IndexedType &other);
        IndexedType();

        int count() const;
        virtual int offset(int index) const;
        int offsetIndex(int offset) const;

        virtual Type *index(int index) = 0;
        Type *index(int width, int offset, std::vector<Member> &memberRefs, std::string &gepValueName, Type *targetField = nullptr);
        virtual Type *replaceIndex(int index, Type *newType);
        IndexedType *indexIndexable(int idx);
        virtual std::string indexName(int index) = 0;
        bool isIndexable() const override;

        Type *indexAs(Type *other, int idx, std::vector<Member> &memberRefs, std::string &gepValueName, std::optional<Type *> bitfield = std::nullopt);
        Type *interpreteAs(Type *other, std::vector<Member> &memberRefs, std::string &loadValueName) override;

    protected:
        int m_count;
        std::vector<int> m_offsets;
    };

    class Void : public Type
    {
    public:
        static Void VOID;

        Void();
        ~Void();

        nlohmann::json toJson() const override;
        std::string toString() const override;
        Kind kind() const override;
        std::string id() const override;
    };

    class Int : public Type
    {
    public:
        Int(int width);
        ~Int() override;

        int width() const;

        nlohmann::json toJson() const override;
        std::string toString() const override;
        Kind kind() const override;
    };

    class Float : public Type
    {
    public:
        Float(int width);
        ~Float() override;

        int width() const;

        nlohmann::json toJson() const override;
        std::string toString() const override;
        Kind kind() const override;
    };

    class Pointer : public Type
    {
    public:
        static Pointer OPAQUE_POINTER;

        Pointer(Type *pointee = nullptr);
        ~Pointer();

        Type *pointee() const;

        std::string id() const override;

        nlohmann::json toJson() const override;
        std::string toString() const override;
        Kind kind() const override;

    private:
        Type *m_pointee;
    };

    class Array : public IndexedType
    {
    public:
        Array(Type *element, int count);
        Array(llvm::Module *module, llvm::Type *llvmType);
        Array(llvm::DICompositeType *diCT, std::vector<int> &dimensions);

        Type *element() const;
        Type *index(int index) override;
        Type *replaceIndex(int index, Type *newType) override;
        std::string indexName(int index) override;
        int offset(int index) const override;

        std::string id() const override;

        nlohmann::json toJson() const override;
        std::string toString() const override;
        Kind kind() const override;

    private:
        Type *m_element;
    };

    class Struct : public IndexedType
    {
    public:
        // Struct(const std::vector<std::tuple<std::string, Type *>> &members);
        Struct(llvm::Module *module, llvm::Type *llvmType);
        Struct(llvm::DICompositeType *diCT, bool isDeclaration = false);

        std::vector<std::tuple<std::string, Type *>> members() const;

        Type *index(int index) override;
        std::string indexName(int index) override;
        Type *replaceIndex(int index, Type *newType) override;
        int size() override;

        bool isDeclaration() const override;
        std::string toString() const override;
        nlohmann::json toJson() const override;
        nlohmann::json toDebugJson() const override;
        std::string id() const override;
        Kind kind() const override;
        std::string name() const;

    private:
        std::vector<std::tuple<std::string, Type *>> m_members;
        std::string m_name;
        bool m_isDeclaration;
    };

    class Bitfield : public Type
    {
    public:
        Bitfield(int offset, int width);
        Bitfield();

        int offset() const;
        int width() const;

        nlohmann::json toJson() const override;
        std::string toString() const override;
        Kind kind() const override;

    private:
        int m_offset;
        int m_width;
    };

    class Union : public Type
    {
    public:
        Union(std::string name, const std::vector<std::tuple<std::string, Type *>> &members);
        Union(llvm::DICompositeType *diCT);

        std::string name() const;
        std::vector<std::tuple<std::string, Type *>> members() const;

        nlohmann::json toJson() const override;
        nlohmann::json toDebugJson() const override;
        std::string toString() const override;
        Kind kind() const override;
        std::string id() const override;

    private:
        std::string m_name;
        std::vector<std::tuple<std::string, Type *>> m_members;
    };

    class Enum : public Type
    {
    public:
        Enum(std::string name, std::vector<std::tuple<std::string, int>> members);

        Enum(llvm::DICompositeType *diCT);

        std::string name() const;
        std::vector<std::tuple<std::string, int>> members() const;

        nlohmann::json toJson() const override;
        nlohmann::json toDebugJson() const override;
        Type::Kind kind() const override;
        std::string toString() const override;
        std::string id() const override;

    private:
        std::vector<std::tuple<std::string, int>> m_members;
        std::string m_name;
    };

    class Other : public Type
    {
    public:
        Other(std::string name, int size);

        nlohmann::json toJson() const override;
        std::string toString() const override;
        Kind kind() const override;

    private:
        std::string m_name;
    };
}
