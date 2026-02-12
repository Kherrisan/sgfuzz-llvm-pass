#include "llvm-variable-type.h"

namespace pingu
{
    std::map<llvm::DIType *, Type *> Type::m_diTypeCache = {};
    std::map<llvm::Type *, Type *> Type::m_typeCache = {};
    std::map<std::string, Type *> Type::m_namedStructCache = {};
    std::map<std::string, Type *> Type::m_idCache = {};
    std::vector<llvm::DIType *> Type::m_diTypeParsingStack = {};
    std::vector<Type *> Type::m_declarationTypes = {};

    bool Type::isFromType(Type *type)
    {
        for (auto &[llvmType, cachedType] : m_typeCache)
        {
            if (cachedType == type)
            {
                return true;
            }
        }
        return false;
    }

    bool Type::isFromDIType(Type *type)
    {
        for (auto &[diType, cachedType] : m_diTypeCache)
        {
            if (cachedType == type)
            {
                return true;
            }
        }
        return false;
    }

    Type *Type::fromName(std::string name)
    {
        ENV_DEBUG(dbgs() << "fromName: " << name << "\n");
        if (m_namedStructCache.find(name) != m_namedStructCache.end())
        {
            ENV_DEBUG(dbgs() << "fromName cache hit: " << m_namedStructCache[name]->toString() << "\n");
            return m_namedStructCache[name];
        }
        return nullptr;
    }

    Type *Type::fromType(llvm::Module *module, llvm::Type *llvmType)
    {
        // ENV_DEBUG(dbgs() << "fromType: " << *llvmType << "\n");
        if (m_typeCache.find(llvmType) != m_typeCache.end())
        {
            // ENV_DEBUG(dbgs() << "fromType from cache: " << m_typeCache[llvmType]->toString() << "\n");
            return m_typeCache[llvmType];
        }
        Type *type = nullptr;

        if (llvmType->isStructTy())
        {
            type = new Struct(module, llvmType);
        }
        else if (llvmType->isArrayTy())
        {
            type = new Array(module, llvmType);
        }
        else if (llvmType->isPointerTy())
        {
            // opaque pointer
            type = &Pointer::OPAQUE_POINTER;
        }
        else if (llvmType->isIntegerTy())
        {
            type = new Int(llvmType->getIntegerBitWidth());
        }
        else if (llvmType->isFloatingPointTy())
        {
            type = new Float(llvmType->getPrimitiveSizeInBits());
        }
        else
        {
            // For other types, like vector (<2 x i32>), we do not support them yet
            return nullptr;
        }

        m_typeCache[llvmType] = type;
        m_idCache[type->id()] = type;
        ENV_DEBUG(dbgs() << "fromType returns: " << type->toString() << "\n");
        return type;
    }

    Type *Type::fromDIType(llvm::DIType *diType)
    {
        // ENV_DEBUG(dbgs() << "fromDIType: " << getDITypeString(diType) << "\n");
        // Check if the DIType is already in the parsing stack
        bool inStack = false;
        if (std::find(m_diTypeParsingStack.begin(), m_diTypeParsingStack.end(), diType) != m_diTypeParsingStack.end())
        {
            // ENV_DEBUG(dbgs() << "fromDIType in stack: " << getDITypeString(diType) << "\n");
            inStack = true;
        }
        if (!diType)
        {
            return &Void::VOID;
        }
        if (m_diTypeCache.find(diType) != m_diTypeCache.end())
        {
            // ENV_DEBUG(dbgs() << "fromDIType cache hit: " << m_diTypeCache[diType]->toString() << "\n");
            // ENV_DEBUG(dbgs() << "fromDIType cache hit is declaration: " << m_diTypeCache[diType]->isDeclaration() << "\n");
            return m_diTypeCache[diType];
        }
        m_diTypeParsingStack.push_back(diType);
        if (auto *derivedDIType = llvm::dyn_cast<llvm::DIDerivedType>(diType))
        {
            if (derivedDIType->getTag() == llvm::dwarf::DW_TAG_member && derivedDIType->getFlags() & llvm::DINode::FlagBitField)
            {
                auto type = new Bitfield(derivedDIType->getOffsetInBits(), derivedDIType->getSizeInBits());
                m_diTypeCache[diType] = type;
                m_idCache[type->id()] = type;
                m_diTypeParsingStack.pop_back();
                return type;
            }
        }
        Type *type = nullptr;
        std::string typedefName = canonicalizeTypedefDIType(diType);
        ENV_DEBUG(dbgs() << "fromDIType after canonicalizeTypedefDIType: " << getDITypeString(diType) << ", typedefName: " << typedefName << "\n");
        if (!diType)
        {
            type = &Void::VOID;
        }
        else if (auto derivedType = llvm::dyn_cast<llvm::DIDerivedType>(diType))
        {
            if (derivedType->getTag() == llvm::dwarf::DW_TAG_ptr_to_member_type)
            {
                // If the member is a pointer to a member function, return a pointer to void
                m_diTypeParsingStack.pop_back();
                int size = derivedType->getSizeInBits();
                return fromTypeID(new Other("DW_TAG_ptr_to_member_type", size));
            }
            if (derivedType->getTag() == llvm::dwarf::DW_TAG_pointer_type || derivedType->getTag() == llvm::dwarf::DW_TAG_reference_type || derivedType->getTag() == llvm::dwarf::DW_TAG_rvalue_reference_type)
            {
                type = new Pointer(Type::fromDIType(derivedType->getBaseType()));
            }
        }
        else if (auto diCompositeType = llvm::dyn_cast<llvm::DICompositeType>(diType))
        {
            if (diCompositeType->getTag() == llvm::dwarf::DW_TAG_structure_type || diCompositeType->getTag() == llvm::dwarf::DW_TAG_class_type)
            {
                bool declaredStruct = inStack || (diCompositeType->getFlags() & llvm::DINode::FlagFwdDecl);
                ENV_DEBUG(dbgs() << "fromDIType declaredStruct: " << declaredStruct << "\n");
                type = new Struct(diCompositeType, declaredStruct);
                if (!declaredStruct && type->name() != "")
                {
                    ENV_DEBUG(dbgs() << "fromDIType adding to namedStructCache: " << type->name() << "\n");
                    ENV_DEBUG(dbgs() << "fromDIType type: " << type->toJson().dump() << "\n");
                    m_namedStructCache[type->name()] = type;
                }
            }
            else if (diCompositeType->getTag() == llvm::dwarf::DW_TAG_array_type)
            {
                std::vector<int> dimensions;
                for (const auto &element : diCompositeType->getElements())
                {
                    auto subrange = llvm::dyn_cast<llvm::DISubrange>(element);
                    auto *CI = llvm::dyn_cast<llvm::ConstantInt *>(subrange->getCount());
                    if (CI)
                    {
                        dimensions.push_back(CI->getZExtValue());
                    }
                    else
                    {
                        dimensions.push_back(-1);
                    }
                }
                type = new Array(diCompositeType, dimensions);
            }
            else if (diCompositeType->getTag() == llvm::dwarf::DW_TAG_union_type)
            {
                type = new Union(diCompositeType);
                if (type->name() != "")
                {
                    m_namedStructCache[type->name()] = type;
                }
            }
            else if (diCompositeType->getTag() == llvm::dwarf::DW_TAG_enumeration_type)
            {
                type = new Enum(diCompositeType);
                if (type->name() != "")
                {
                    m_namedStructCache[type->name()] = type;
                }
            }
            else
            {
                assert(false && "Unsupported DICompositeType");
            }
        }
        else if (auto BT = llvm::dyn_cast<llvm::DIBasicType>(diType))
        {
            if (BT->getName().contains("float") || BT->getName().contains("double"))
            {
                type = new Float(BT->getSizeInBits());
            }
            else
            {
                type = new Int(BT->getSizeInBits());
            }
        }
        else if (auto *subroutineType = llvm::dyn_cast<llvm::DISubroutineType>(diType))
        {
            type = &Void::VOID;
        }
        else
        {
            assert(false && "Unsupported DIType");
        }
        type->m_typedefName = typedefName;
        if (!typedefName.empty())
        {
            m_namedStructCache[typedefName] = type;
        }
        m_diTypeCache[diType] = type;
        m_idCache[type->id()] = type;
        m_diTypeParsingStack.pop_back();
        ENV_DEBUG(dbgs() << "fromDIType returns: " << type->toString() << "\n");
        return type;
    }

    std::vector<Type *> &Type::declareTypes()
    {
        return m_declarationTypes;
    }

    Type *Type::fromTypeID(Type *type)
    {
        // ENV_DEBUG(dbgs() << "fromTypeID: " << type->toString() << "\n");
        std::string id = type->id();
        if (m_idCache.find(id) != m_idCache.end())
        {
            delete type;
            // ENV_DEBUG(dbgs() << "fromTypeID cache hit: " << m_idCache[id]->toString() << "\n");
            return m_idCache[id];
        }
        else
        {
            m_idCache[id] = type;
        }
        return type;
    }

    bool Type::isIndexable() const
    {
        return false;
    }

    Type *Type::interpreteAs(Type *other, std::vector<Member> &memberRefs, std::string &loadValueName)
    {
        if (other == &Pointer::OPAQUE_POINTER)
        {
            if (kind() == Kind::Pointer)
            {
                return this;
            }
        }
        return other;
    }

    nlohmann::json Type::toDebugJson() const
    {
        return toJson();
    }

    std::string Type::name() const
    {
        switch (kind())
        {
        case Kind::Struct:
            return static_cast<const Struct *>(this)->name();
        case Kind::Union:
            return static_cast<const Union *>(this)->name();
        case Kind::Enum:
            return static_cast<const Enum *>(this)->name();
        default:
            ENV_DEBUG(dbgs() << "Type without name: " << toString() << "\n");
            return "";
        }
    }

    bool Type::isDeclaration() const { return false; }

    std::string Type::typedefName() const { return m_typedefName; }

    int Type::size() { return m_size; }

    std::string Type::id() const
    {
        return toString();
    }

    Type::Type() {}

    Type::Type(const Type &other) : m_typedefName(other.m_typedefName), m_size(other.m_size) {}

    std::ostream &operator<<(std::ostream &os, const Type &type)
    {
        os << type.toString();
        return os;
    }

    IndexedType::IndexedType(int count, int size) : m_count(count) {}
    IndexedType::IndexedType() : m_count(0) {}

    Type *IndexedType::replaceIndex(int index, Type *newType)
    {
        return this->index(index);
    }

    int IndexedType::count() const { return m_count; }

    int IndexedType::offset(int index) const { return m_offsets.at(index); }

    int IndexedType::offsetIndex(int offset) const
    {
        for (int i = m_count - 1; i >= 0; i--)
        {
            if (m_offsets.at(i) <= offset)
            {
                return i;
            }
        }
        return -1;
    }

    IndexedType::IndexedType(const IndexedType &other) : m_count(other.m_count), m_offsets(other.m_offsets) {}

    IndexedType *IndexedType::indexIndexable(int idx)
    {
        auto indexable = index(idx);
        if (indexable->isIndexable())
        {
            return static_cast<IndexedType *>(indexable);
        }
        return nullptr;
    }

    Type *IndexedType::index(int targetWidth, int targetOffset, std::vector<Member> &memberRefs, std::string &gepValueName, Type *targetField)
    {
        assert(targetOffset >= 0);
        assert(this->isIndexable());
        for (int i = 0; i < count(); i++)
        {
            int fieldOffset = this->offset(i);
            auto field = index(i);
            if (!field)
            {
                ENV_DEBUG(dbgs() << "[!] Failed to index " << i << "th field of " << toString() << "\n");
                return nullptr;
            }
            ENV_DEBUG(dbgs() << "index field: " << field->toString() << "\n");

            if (field->isDeclaration())
            {
                auto typeDef = Type::fromName(field->name());
                if (!typeDef)
                {
                    dbgs() << "[!] sg-source-pass: failed to find definition of: '" << field->name() << "'\n";
                }
                else
                {
                    replaceIndex(i, typeDef);
                    field = typeDef;
                }
            }
            int fieldWidth = field->size();
            if (field->isIndexable() && !field->isDeclaration())
            {
                auto indexedType = static_cast<IndexedType *>(field);
                int lastIdx = indexedType->count() - 1;
                if (lastIdx > 0)
                {
                    fieldWidth = indexedType->offset(lastIdx) + indexedType->index(lastIdx)->size();
                }
            }
            auto fieldName = indexName(i);
            ENV_DEBUG(dbgs() << "index fieldName: " << fieldName << ", fieldOffset: " << fieldOffset << ", fieldWidth: " << fieldWidth << "\n");
            if (fieldWidth <= 0)
            {
                // This field is an array of unknown dimension size.
                fieldWidth = targetWidth;
            }
            if (fieldOffset <= targetOffset && targetOffset < fieldOffset + fieldWidth)
            {
                // the field indexed falls within [offset, offset + width)
                if (isPrefixWithOnlyDigits(fieldName, gepValueName) || fieldWidth == targetWidth)
                {
                    // this type and other type are matched
                    ENV_DEBUG(dbgs() << "index matched, fieldName: " << fieldName << ", offset: " << fieldOffset << ", size: " << fieldWidth << ", type: " << index(i)->toString() << "\n");
                    if (fieldName.find(ARRAY_INDEXED_NAME) == std::string::npos)
                    {
                        memberRefs.push_back(std::make_tuple(fieldName, field));
                    }
                    else if (memberRefs.size() > 0)
                    {
                        // this is an array, and field is the array element
                        auto [arrayName, arrayType] = memberRefs.back();
                        memberRefs.push_back(std::make_tuple(arrayName, field));
                    }
                    return field;
                }
                else if (targetWidth < fieldWidth && field->isIndexable())
                {
                    // the field indexed falls within [offset, offset + width)
                    // which is wider than the field indexed
                    // For example:
                    // GPE ptr, {i64, ptr} %1, 0, 1, where %1 is {ptr, {ptr, ptr}}
                    // => indexAs({ptr, ptr}, 64, 64 - 64)
                    if (fieldName.find(ARRAY_INDEXED_NAME) == std::string::npos)
                    {
                        memberRefs.push_back(std::make_tuple(fieldName, field));
                    }
                    else if (memberRefs.size() > 0)
                    {
                        // this is an array, and field is the array element
                        auto [arrayName, arrayType] = memberRefs.back();
                        memberRefs.push_back(std::make_tuple(arrayName, field));
                    }
                    auto fieldIndexable = static_cast<IndexedType *>(field);
                    return fieldIndexable->index(targetWidth, targetOffset - fieldOffset, memberRefs, gepValueName, targetField);
                }
                else if (targetField)
                {
                    // fieldWidth is smaller than width
                    // or the field is not indexable
                    // return member name and the other type as the indexing result
                    memberRefs.push_back(std::make_tuple(fieldName, targetField));
                    return targetField;
                }
                else
                {
                    assert(false && "Failed to index target field");
                }
            }
            else if (fieldOffset > targetOffset)
            {
                ENV_DEBUG(dbgs() << "[!] Found index field offset greater than target offset\n");
                ENV_DEBUG(dbgs() << "[!] Missing the target offset in field list\n");
                return nullptr;
            }
        }
        ENV_DEBUG(dbgs() << "[!] Failed to index target field\n");
        return nullptr;
    }

    Type *IndexedType::indexAs(Type *other, int idx, std::vector<Member> &memberRefs, std::string &gepValueName, std::optional<Type *> bitfield)
    {
        ENV_DEBUG(dbgs() << "indexAs other type: " << other->toString() << ", idx: " << idx << "\n");
        ENV_DEBUG(dbgs() << "indexAs this type: " << toString() << "\n");

        // TODO: remove this check ?
        if (other->isDeclaration())
        {
            ENV_DEBUG(dbgs() << "indexAs other is declaration\n");
            std::string name = other->name();
            other = Type::fromName(other->name());
            if (!other)
            {
                ENV_DEBUG(dbgs() << "indexAs failed to find definition of: '" << name << "'\n");
                return nullptr;
            }
        }
        auto indexable = static_cast<IndexedType *>(other);
        assert(indexable);
        auto targetField = indexable->index(idx);
        if (!targetField)
        {
            ENV_DEBUG(dbgs() << "[!] Failed to index " << idx << "th field of " << indexable->toString() << "\n");
            return nullptr;
        }
        auto targetOffset = indexable->offset(idx);
        auto targetWidth = targetField->size();
        // TODO: remove this check ?
        if (targetOffset == 0 && targetWidth == size())
        {
            return this;
        }
        ENV_DEBUG(dbgs() << "indexAs target field: " << targetField->toString() << ", target offset: " << targetOffset << ", target width: " << targetWidth << "\n");
        if (bitfield)
        {
            targetWidth = static_cast<Bitfield *>(*bitfield)->width();
            targetOffset += static_cast<Bitfield *>(*bitfield)->offset();
            ENV_DEBUG(dbgs() << "indexAs bitfield in struct, width: " << targetWidth << ", offset: " << targetOffset << "\n");
        }
        if (targetWidth == 0)
        {
            // For example:
            // %arrayidx = getelementptr [0 x %struct.ecc_set_type], ptr @ecc_sets, i64 0, i64 %idxprom
            ENV_DEBUG(dbgs() << "index target field width is 0\n");
            // TODO:
            return this;
        }
        auto fieldType = index(targetWidth, targetOffset, memberRefs, gepValueName, targetField);
        if (!fieldType)
        {
            ENV_DEBUG(dbgs() << "[!] Failed to index the field(name: " << gepValueName << ", width: " << targetWidth << ", offset: " << targetOffset << ") in " << toString() << "\n");
            return nullptr;
        }
        if (bitfield && fieldType->kind() == Type::Kind::Bitfield)
        {
            auto [fieldName, fieldType] = memberRefs.back();
            memberRefs.pop_back();
            memberRefs.push_back(std::make_tuple(fieldName, *bitfield));
        }
        return fieldType;
    }

    Type *IndexedType::interpreteAs(Type *other, std::vector<Member> &memberRefs, std::string &loadValueName)
    {
        ENV_DEBUG(dbgs() << "interpreteAs: " << other->toString() << "\n");
        if (other->isDeclaration())
        {
            other = Type::fromName(other->name());
        }
        if (size() < other->size())
        {
            return nullptr;
        }
        else
        {
            if (!other->isIndexable())
            {
                if (!this->isIndexable())
                {
                    return nullptr;
                }
                Type *firstMemberType = index(0);
                if (!firstMemberType)
                {
                    ENV_DEBUG(dbgs() << "[!] Failed to index 0th field of " << toString() << "\n");
                    return nullptr;
                }
                if (firstMemberType->size() < other->size())
                {
                    return nullptr;
                }
                else if (firstMemberType->size() == other->size())
                {
                    memberRefs.push_back(std::make_tuple(indexName(0), firstMemberType));
                    return firstMemberType;
                }
                else
                {
                    memberRefs.push_back(std::make_tuple(indexName(0), firstMemberType));
                    auto child = indexIndexable(0)->interpreteAs(other, memberRefs, loadValueName);
                    if (!child)
                    {
                        memberRefs.pop_back();
                        return nullptr;
                    }
                    else
                    {
                        return child;
                    }
                }
            }
            // Both this type and the other type are indexable (array or struct)
            auto otherIndexable = static_cast<IndexedType *>(other);
            auto thisIndexable = static_cast<IndexedType *>(this);
            if (count() < otherIndexable->count())
            {
                return nullptr;
            }
            else
            {
                bool matched = true;
                for (int i = 0; i < otherIndexable->count(); i++)
                {
                    auto otherMemberType = otherIndexable->index(i);
                    if (!otherMemberType)
                    {
                        ENV_DEBUG(dbgs() << "[!] Failed to index " << i << "th field of " << other->toString() << "\n");
                        return nullptr;
                    }
                    auto thisMemberType = thisIndexable->index(i);
                    if (!thisMemberType)
                    {
                        ENV_DEBUG(dbgs() << "[!] Failed to index " << i << "th field of " << toString() << "\n");
                        return nullptr;
                    }
                    if (offset(i) == otherIndexable->offset(i) && thisMemberType->size() == otherMemberType->size())
                    {
                        continue;
                    }
                    matched = false;
                    break;
                }
                if (matched)
                {
                    // this type and the other type are matched
                    return this;
                }
                else
                {
                    // try to interprete the first field of this type as the other type
                    memberRefs.push_back(std::make_tuple(indexName(0), thisIndexable->index(0)));
                    auto child = thisIndexable->indexIndexable(0)->interpreteAs(other, memberRefs, loadValueName);
                    if (!child)
                    {
                        memberRefs.pop_back();
                        return nullptr;
                    }
                    else
                    {
                        return child;
                    }
                }
            }
        }
    }

    bool IndexedType::isIndexable() const
    {
        return true;
    }

    Void Void::VOID;

    Void::Void()
    {
        m_size = 0;
    }

    Void::~Void() {}

    Type::Kind Void::kind() const { return Type::Kind::Void; }

    nlohmann::json Void::toJson() const
    {
        if (m_typedefName.empty())
        {
            return nlohmann::json{
                {"type", "void"}};
        }
        else
        {
            return nlohmann::json{
                {"type", "void"},
                {"typedef", m_typedefName}};
        }
    }

    std::string Void::id() const
    {
        return "void";
    }

    std::string Void::toString() const
    {
        if (m_typedefName.empty())
        {
            return "void";
        }
        else
        {
            return "typedef " + m_typedefName + " void";
        }
    }

    Int::Int(int width)
    {
        m_size = width;
    }

    Int::~Int() {}

    int Int::width() const { return m_size; }

    Type::Kind Int::kind() const { return Type::Kind::Int; }

    nlohmann::json Int::toJson() const
    {
        if (m_typedefName.empty())
        {
            return nlohmann::json{
                {"type", "int"},
                {"width", m_size}};
        }
        else
        {
            return nlohmann::json{
                {"type", "int"},
                {"typedef", m_typedefName},
                {"width", m_size}};
        }
    }

    std::string Int::toString() const
    {
        if (m_typedefName.empty())
        {
            return "i" + std::to_string(m_size);
        }
        else
        {
            return "typedef " + m_typedefName + " i" + std::to_string(m_size);
        }
    }

    Float::Float(int width)
    {
        m_size = width;
    }

    Float::~Float() {}

    int Float::width() const { return m_size; }

    Type::Kind Float::kind() const { return Type::Kind::Float; }

    nlohmann::json Float::toJson() const
    {
        if (m_typedefName.empty())
        {
            return nlohmann::json{
                {"type", "float"},
                {"width", m_size}};
        }
        else
        {
            return nlohmann::json{
                {"type", "float"},
                {"typedef", m_typedefName},
                {"width", m_size}};
        }
    }

    std::string Float::toString() const
    {
        if (m_typedefName.empty())
        {
            return "f" + std::to_string(m_size);
        }
        else
        {
            return "typedef " + m_typedefName + " f" + std::to_string(m_size);
        }
    }

    Pointer Pointer::OPAQUE_POINTER(&Void::VOID);

    Pointer::Pointer(Type *pointee) : m_pointee(pointee)
    {
        m_size = sizeof(void *) * 8;
    }

    Pointer::~Pointer() {}

    Type *Pointer::pointee() const { return m_pointee; }

    Type::Kind Pointer::kind() const { return Type::Kind::Pointer; }

    std::string Pointer::id() const
    {
        return m_pointee->id() + "*";
    }

    nlohmann::json Pointer::toJson() const
    {
        if (m_typedefName.empty())
        {
            return nlohmann::json{
                {"type", "pointer"},
                {"pointee", m_pointee->toJson()}};
        }
        else
        {
            return nlohmann::json{
                {"type", "pointer"},
                {"typedef", m_typedefName},
                {"pointee", m_pointee->toJson()}};
        }
    }

    std::string Pointer::toString() const
    {
        if (m_typedefName.empty())
        {
            return "" + m_pointee->toString() + "*";
        }
        else
        {
            return "typedef " + m_typedefName + " (" + m_pointee->toString() + "*)";
        }
    }

    Array::Array(Type *element, int count) : m_element(element)
    {
        m_count = count;
        m_size = m_element->size() * m_count;
        for (int i = 0; i < m_count; i++)
        {
            m_offsets.push_back(i * m_element->size());
        }
    }

    Array::Array(llvm::Module *module, llvm::Type *llvmType)
    {
        assert(llvmType->isArrayTy());
        m_element = Type::fromType(module, llvmType->getArrayElementType());
        m_count = llvmType->getArrayNumElements();
        for (int i = 0; i < m_count; i++)
        {
            m_offsets.push_back(i * m_element->size());
        }
        m_size = m_element->size() * m_count;
    }

    Array::Array(llvm::DICompositeType *diCT, std::vector<int> &dimensions)
    {
        ENV_DEBUG(dbgs() << "Array::Array(llvm::DICompositeType *diCT, std::vector<int> &dimensions): " << getDITypeString(diCT) << "\n");
        ENV_DEBUG(dbgs() << "dimensions: "; for (auto d : dimensions) { dbgs() << d << " "; } dbgs() << "\n");
        assert(diCT->getTag() == llvm::dwarf::DW_TAG_array_type);
        m_count = dimensions.at(0);
        dimensions.erase(dimensions.begin());
        if (dimensions.size() > 0)
        {
            m_element = new Array(diCT, dimensions);
            if (m_element->size() != -1)
            {
                for (int i = 0; i < m_count; i++)
                {
                    m_offsets.push_back(i * m_element->size());
                }
            }
        }
        else
        {
            m_element = Type::fromDIType(diCT->getBaseType());
            if (m_element->size() != -1)
            {
                for (int i = 0; i < m_count; i++)
                {
                    m_offsets.push_back(i * m_element->size());
                }
            }
        }
        m_size = m_element->size() * m_count;
    }

    Type *Array::element() const { return m_element; }

    Type *Array::index(int index)
    {
        return m_element;
    }

    Type::Kind Array::kind() const { return Type::Kind::Array; }

    std::string Array::indexName(int index)
    {
        return ARRAY_INDEXED_NAME;
    }

    Type *Array::replaceIndex(int index, Type *newType)
    {
        auto oldType = m_element;
        m_element = newType;
        return oldType;
    }

    int Array::offset(int index) const
    {
        return m_element->size() * index;
    }

    std::string Array::id() const
    {
        return m_element->id() + "[" + std::to_string(m_count) + "]";
    }

    nlohmann::json Array::toJson() const
    {
        nlohmann::json json;
        if (m_size == -1)
        {
            json = nlohmann::json{
                {"type", "array"},
                {"element", m_element->toJson()}};
        }
        else
        {
            json = nlohmann::json{
                {"type", "array"},
                {"element", m_element->toJson()},
                {"size", m_size}};
        }
        if (!m_typedefName.empty())
        {
            json["typedef"] = m_typedefName;
        }
        return json;
    }

    std::string Array::toString() const
    {
        auto arrayName = m_element->toString() + "[" + std::to_string(m_count) + "]";
        if (m_typedefName.empty())
        {
            return arrayName;
        }
        else
        {
            return "typedef " + m_typedefName + " (" + arrayName + ")";
        }
    }

    Struct::Struct(llvm::Module *module, llvm::Type *llvmType)
    {
        llvm::DataLayout dataLayout(module);
        auto structLayout = dataLayout.getStructLayout(llvm::dyn_cast<llvm::StructType>(llvmType));
        assert(llvmType->isStructTy());
        m_name = pruneStructName(llvmType->getStructName().str());
        m_count = llvmType->getStructNumElements();
        m_size = structLayout->getSizeInBits();
        m_isDeclaration = false;
        ENV_DEBUG(dbgs() << "m_size: " << m_size << "\n");
        for (int i = 0; i < m_count; i++)
        {
            auto element = llvmType->getStructElementType(i);
            int offset = structLayout->getElementOffset(i).getFixedValue() * 8;
            m_offsets.push_back(offset);
            m_members.push_back(std::make_tuple("", Type::fromType(module, element)));
        }
    }

    Struct::Struct(llvm::DICompositeType *diCT, bool isDeclaration)
    {
        assert(diCT->getTag() == llvm::dwarf::DW_TAG_structure_type || diCT->getTag() == llvm::dwarf::DW_TAG_class_type);
        m_name = diCT->getName();
        m_size = diCT->getSizeInBits(); // getSizeInBits() may return the wrong size
        if (isDeclaration)
        {
            // m_size = diCT->getSizeInBits();
            Type::declareTypes().push_back(this);
            ENV_DEBUG(dbgs() << "Struct::Struct(llvm::DICompositeType *diCT), isDeclaration, size: " << m_size << "\n");
            m_isDeclaration = true;
            return;
        }
        m_isDeclaration = false;
        for (const auto &member : diCT->getElements())
        {
            auto structMember = llvm::dyn_cast<llvm::DIDerivedType>(member);
            if (!structMember)
            {
                // If the member is a DISubprogram, we skip it
                continue;
            }
            if (structMember->getTag() == llvm::dwarf::DW_TAG_inheritance)
            {
                auto inheritanceTy = llvm::dyn_cast<llvm::DICompositeType>(structMember->getBaseType());
                if (inheritanceTy && inheritanceTy->getSizeInBits() <= 8)
                {
                    continue;
                }
            }
            if (structMember->getFlags() & llvm::DINode::FlagStaticMember)
            {
                continue;
            }
            auto name = structMember->getName().str();
            Type *type;
            if (structMember->getFlags() & llvm::DINode::FlagBitField)
            {
                type = Type::fromTypeID(new Bitfield(structMember->getOffsetInBits(), structMember->getSizeInBits()));
            }
            else
            {
                type = Type::fromDIType(structMember->getBaseType());
            }
            ENV_DEBUG(dbgs() << "Struct::Struct(llvm::DICompositeType *diCT): " << m_name << ", member: " << name << ", DIType: " << getDITypeString(structMember->getBaseType()) << "\n");
            ENV_DEBUG(dbgs() << "Struct::Struct(llvm::DICompositeType *diCT): " << m_name << ", member: " << name << ", type: " << type->toString() << "\n");
            auto offset = structMember->getOffsetInBits();
            m_offsets.push_back(offset);
            m_members.push_back(std::make_tuple(name, type));
            // size += type->size();
            m_count++;
        }
        // auto [name, type] = m_members.back();
        // m_size = m_offsets.back() + type->size();
        ENV_DEBUG(dbgs() << "Struct::Struct(llvm::DICompositeType *diCT), size: " << m_size << "\n");
    }

    std::vector<std::tuple<std::string, Type *>> Struct::members() const { return m_members; }

    Type *Struct::replaceIndex(int index, Type *newType)
    {
        auto oldType = std::get<1>(m_members.at(index));
        std::get<1>(m_members.at(index)) = newType;
        return oldType;
    }

    // TODO: based on the number of elements, we can determine if it is a declaration
    bool Struct::isDeclaration() const { return m_isDeclaration; }

    Type *Struct::index(int index)
    {
        return std::get<1>(m_members.at(index));
    }

    std::string Struct::indexName(int index)
    {
        return std::get<0>(m_members.at(index));
    }

    Type::Kind Struct::kind() const { return Type::Kind::Struct; }

    int Struct::size()
    {
        // int lastOffset = m_offsets.back();
        // auto [lastFieldName, lastFieldType] = m_members.back();
        // if (lastFieldType->isDeclaration())
        // {
        //     lastFieldType = Type::fromName(lastFieldType->name());
        //     if (!lastFieldType)
        //     {
        //         ENV_DEBUG(dbgs() << "Struct::size failed to find definition of: " << lastFieldType->name() << "\n");
        //         assert(false);
        //     }
        //     // m_members.pop_back();
        //     // m_members.push_back(std::make_tuple(lastFieldName, lastFieldType));
        // }
        // return lastOffset + lastFieldType->size();
        return m_size;
    }

    nlohmann::json Struct::toJson() const
    {
        nlohmann::json::array_t members;
        for (const auto &member : m_members)
        {
            members.push_back(nlohmann::json{
                {"name", std::get<0>(member)},
                {"type", std::get<1>(member)->toJson()},
            });
        }
        nlohmann::json json{
            {"type", "struct"},
            {"name", m_name}};
        if (!m_typedefName.empty())
        {
            json["typedef"] = m_typedefName;
        }
        return json;
    }

    nlohmann::json Struct::toDebugJson() const
    {
        nlohmann::json::array_t members;
        for (const auto &member : m_members)
        {
            members.push_back(nlohmann::json{
                {"name", std::get<0>(member)},
                {"type", std::get<1>(member)->toJson()},
            });
        }
        return nlohmann::json{
            {"type", "struct"},
            {"name", m_name},
            {"isDeclaration", m_isDeclaration},
            {"members", members}};
    }

    std::string Struct::toString() const
    {
        auto structName = "struct." + m_name;
        if (m_typedefName.empty())
        {
            return structName;
        }
        else
        {
            return "typedef " + m_typedefName + " " + structName;
        }
    }

    std::string Struct::id() const
    {
        std::string id = "struct." + m_name + "{";
        for (const auto &member : m_members)
        {
            id += "," + std::get<1>(member)->id();
        }
        id += "}";
        return id;
    }

    std::string Struct::name() const { return m_name; }

    Bitfield::Bitfield(int offset, int width) : m_offset(offset), m_width(width)
    {
        m_size = m_width;
    }

    Bitfield::Bitfield() : m_offset(0), m_width(0) {}

    int Bitfield::offset() const { return m_offset; }
    int Bitfield::width() const { return m_width; }

    Type::Kind Bitfield::kind() const { return Type::Kind::Bitfield; }

    nlohmann::json Bitfield::toJson() const
    {
        return nlohmann::json{
            {"type", "bitfield"},
            {"offset", m_offset},
            {"width", m_width}};
    }

    std::string Bitfield::toString() const
    {
        return "bitfield(" + std::to_string(m_offset) + ", " + std::to_string(m_width) + ")";
    }

    Union::Union(std::string name, const std::vector<std::tuple<std::string, Type *>> &members) : m_name(name), m_members(members) {}

    Union::Union(llvm::DICompositeType *diCT)
    {
        assert(diCT->getTag() == llvm::dwarf::DW_TAG_union_type);
        m_name = pruneStructName(diCT->getName().str());
        m_size = diCT->getSizeInBits();
        for (const auto &member : diCT->getElements())
        {
            auto unionMember = llvm::dyn_cast<llvm::DIDerivedType>(member);
            assert(unionMember);
            auto name = unionMember->getName().str();
            auto type = Type::fromDIType(unionMember->getBaseType());
            m_members.push_back(std::make_tuple(name, type));
        }
    }

    std::string Union::name() const { return m_name; }

    std::vector<std::tuple<std::string, Type *>> Union::members() const { return m_members; }

    Type::Kind Union::kind() const { return Type::Kind::Union; }

    nlohmann::json Union::toJson() const
    {
        nlohmann::json json{
            {"type", "union"},
            {"name", m_name}};
        if (!m_typedefName.empty())
        {
            json["typedef"] = m_typedefName;
        }
        return json;
    }

    nlohmann::json Union::toDebugJson() const
    {
        nlohmann::json::array_t members;
        for (const auto &member : m_members)
        {
            members.push_back(nlohmann::json{
                {"name", std::get<0>(member)},
                {"type", std::get<1>(member)->toJson()}});
        }
        return nlohmann::json{
            {"type", "union"},
            {"name", m_name},
            {"members", members}};
    }

    std::string Union::toString() const
    {
        auto unionName = "union." + m_name;
        if (m_typedefName.empty())
        {
            return unionName;
        }
        else
        {
            return "typedef " + m_typedefName + " " + unionName;
        }
    }

    std::string Union::id() const
    {
        std::string id = "union." + m_name + "{";
        for (const auto &member : m_members)
        {
            id += "," + std::get<1>(member)->id();
        }
        id += "}";
        return id;
    }

    Enum::Enum(std::string name, std::vector<std::tuple<std::string, int>> members) : m_members(members), m_name(name) {}

    Type::Kind Enum::kind() const { return Type::Kind::Enum; }

    Enum::Enum(llvm::DICompositeType *diCT)
    {
        assert(diCT->getTag() == llvm::dwarf::DW_TAG_enumeration_type);
        m_name = diCT->getName();
        m_size = sizeof(int) * 8;
        for (const auto &member : diCT->getElements())
        {
            auto enumMember = llvm::dyn_cast<llvm::DIEnumerator>(member);
            assert(enumMember);
            m_members.push_back(std::make_tuple(enumMember->getName().str(), static_cast<int>(enumMember->getValue().getZExtValue())));
        }
    }

    std::string Enum::name() const { return m_name; }
    std::vector<std::tuple<std::string, int>> Enum::members() const { return m_members; }

    nlohmann::json Enum::toJson() const
    {
        nlohmann::json json{
            {"type", "enum"},
            {"name", m_name}};
        if (!m_typedefName.empty())
        {
            json["typedef"] = m_typedefName;
        }
        return json;
    }

    nlohmann::json Enum::toDebugJson() const
    {
        nlohmann::json::array_t members;
        for (const auto &member : m_members)
        {
            members.push_back(nlohmann::json{
                {"name", std::get<0>(member)},
                {"value", std::get<1>(member)}});
        }
        return nlohmann::json{
            {"type", "enum"},
            {"name", m_name},
            {"members", members}};
    }

    std::string Enum::toString() const
    {
        auto enumName = "enum." + m_name;
        if (m_typedefName.empty())
        {
            return enumName;
        }
        else
        {
            return "typedef " + m_typedefName + " " + enumName;
        }
    }

    std::string Enum::id() const
    {
        std::string id = "enum." + m_name + "{";
        for (const auto &member : m_members)
        {
            id += "," + std::to_string(std::get<1>(member));
        }
        id += "}";
        return id;
    }

    Other::Other(std::string name, int size)
    {
        m_name = name;
        m_size = size;
    }

    Type::Kind Other::kind() const { return Type::Kind::Other; }

    nlohmann::json Other::toJson() const
    {
        return nlohmann::json{
            {"type", "other"},
            {"name", m_name},
            {"size", m_size}};
    }

    std::string Other::toString() const
    {
        return "other(" + m_name + ", " + std::to_string(m_size) + ")";
    }
}