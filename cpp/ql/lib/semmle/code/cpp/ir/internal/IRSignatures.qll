private import semmle.code.cpp.ir.implementation.IRType

signature module LanguageTypeSig {
  class LanguageType {
    string toString();

    /** Gets a string used in IR dumps */
    string getDumpString();

    /** Gets the size of the type in bytes, if known. */
    int getByteSize();

    /**
     * Holds if the `LanguageType` represents a prvalue of type `type` (if `isGLValue` is `false`), or if
     * it represents a glvalue of type `type` (if `isGLValue` is `true`).
     */
    predicate hasType(OpaqueTypeTag type, boolean isGLValue);

    /**
     * Holds if this type represents the C++ type `type`. If `isGLValue` is `true`, then this type
     * represents a glvalue of type `type`. Otherwise, it represents a prvalue of type `type`.
     */
    predicate hasUnspecifiedType(OpaqueTypeTag type, boolean isGLValue);
  }

  /**
   * The underlying type of types from the language that this IR type is based on.
   */
  class OpaqueTypeTag {
    string toString();
  }

  class TypeDomainType;

  class RealDomainType extends TypeDomainType;

  class ComplexDomainType extends TypeDomainType;

  class ImaginaryDomainType extends TypeDomainType;

  /**
   * Holds if an `IRErrorType` should exist.
   */
  predicate hasErrorType();

  /**
   * Holds if an `IRBooleanType` with the specified `byteSize` should exist.
   */
  predicate hasBooleanType(int byteSize);

  /**
   * Holds if an `IRSignedIntegerType` with the specified `byteSize` should exist.
   */
  predicate hasSignedIntegerType(int byteSize);

  /**
   * Holds if an `IRUnsignedIntegerType` with the specified `byteSize` should exist.
   */
  predicate hasUnsignedIntegerType(int byteSize);

  /**
   * Holds if an `IRFloatingPointType` with the specified size, base, and type domain should exist.
   */
  predicate hasFloatingPointType(int byteSize, int base, TypeDomainType domain);

  /**
   * Holds if an `IRAddressType` with the specified `byteSize` should exist.
   */
  predicate hasAddressType(int byteSize);

  /**
   * Holds if an `IRFunctionAddressType` with the specified `byteSize` should exist.
   */
  predicate hasFunctionAddressType(int byteSize);

  /**
   * Holds if an `IROpaqueType` with the specified `tag` and `byteSize` should exist.
   */
  predicate hasOpaqueType(OpaqueTypeTag tag, int byteSize);

  LanguageType getUnknownType();

  LanguageType getVoidType();

  LanguageType getTypeForPRValue(OpaqueTypeTag type);

  /**
   * Gets the `LanguageType` that represents a prvalue of type `type`, if such a `LanguageType` exists.
   * Otherwise, gets `CppUnknownType`.
   */
  LanguageType getTypeForPRValueOrUnknown(OpaqueTypeTag type);

  /**
   * Gets the `LanguageType` that represents a glvalue of type `type`.
   */
  LanguageType getTypeForGLValue(OpaqueTypeTag type);

  /**
   * Gets the `LanguageType` that represents a prvalue of type `int`.
   */
  LanguageType getIntType();

  /**
   * Gets the `LanguageType` that represents a prvalue of type `bool`.
   */
  LanguageType getBoolType();

  /**
   * Gets the `LanguageType` that represents a glvalue of type `bool`.
   */
  LanguageType getBoolGLValueType();

  /**
   * Gets the `LanguageType` that represents a glvalue of function type.
   */
  LanguageType getFunctionGLValueType();

  /**
   * Gets the `LanguageType` that represents a opaque of unknown type with size `byteSize`.
   */
  LanguageType getUnknownOpaqueType(int byteSize);

  /**
   * Gets the `LanguageType` that is the canonical type for an `IRBooleanType` with the specified
   * `byteSize`.
   */
  LanguageType getCanonicalBooleanType(int byteSize);

  /**
   * Gets the `LanguageType` that is the canonical type for an `IRSignedIntegerType` with the specified
   * `byteSize`.
   */
  LanguageType getCanonicalSignedIntegerType(int byteSize);

  /**
   * Gets the `LanguageType` that is the canonical type for an `IRUnsignedIntegerType` with the specified
   * `byteSize`.
   */
  LanguageType getCanonicalUnsignedIntegerType(int byteSize);

  /**
   * Gets the `LanguageType` that is the canonical type for an `IRFloatingPointType` with the specified
   * size, base, and type domain.
   */
  LanguageType getCanonicalFloatingPointType(int byteSize, int base, TypeDomainType domain);

  /**
   * Gets the `LanguageType` that is the canonical type for an `IRAddressType` with the specified
   * `byteSize`.
   */
  LanguageType getCanonicalAddressType(int byteSize);

  /**
   * Gets the `LanguageType` that is the canonical type for an `IRFunctionAddressType` with the specified
   * `byteSize`.
   */
  LanguageType getCanonicalFunctionAddressType(int byteSize);

  /**
   * Gets the `LanguageType` that is the canonical type for `IRErrorType`.
   */
  LanguageType getCanonicalErrorType();

  /**
   * Gets the `LanguageType` that is the canonical type for `IRUnknownType`.
   */
  LanguageType getCanonicalUnknownType();

  /**
   * Gets the `LanguageType` that is the canonical type for `IRVoidType`.
   */
  LanguageType getCanonicalVoidType();

  /**
   * Gets the `LanguageType` that is the canonical type for an `IROpaqueType` with the specified `tag` and
   * `byteSize`.
   */
  LanguageType getCanonicalOpaqueType(OpaqueTypeTag tag, int byteSize);

  /**
   * Gets a string that uniquely identifies an `IROpaqueType` tag. This may be different from the usual
   * `toString()` of the tag in order to ensure uniqueness.
   */
  string getOpaqueTagIdentityString(OpaqueTypeTag tag);
}

signature module LanguageSig {
  class Function;

  class Location;

  class UnknownLocation extends Location;

  class UnknownDefaultLocation extends Location;

  class File;

  class AST;

  class Type;

  class UnknownType extends Type;

  class VoidType extends Type;

  class IntegralType extends Type;

  class FloatingPointType extends Type;

  // REVIEW: May need to synthesize this for other languages. Or do we really need it at all?
  class ClassDerivation;

  class StringLiteral;

  class Variable;

  class AutomaticVariable extends Variable;

  class StaticVariable extends Variable;

  class GlobalVariable extends Variable;

  class Parameter extends Variable;

  class Field extends Variable;

  class BuiltInOperation;

  class Declaration;

  // TODO: Remove necessity for these.
  class Expr;

  class Class; // Used for inheritance conversions

  predicate hasCaseEdge(string minValue, string maxValue);

  predicate hasPositionalArgIndex(int argIndex);

  predicate hasAsmOperandIndex(int operandIndex);

  int getTypeSize(Type type);

  int getPointerSize();

  string getStringLiteralText(StringLiteral s);

  predicate hasPotentialLoop(Function f);

  predicate hasGoto(Function f);

  /**
   * Gets the offset of field `field` in bits.
   */
  int getFieldBitOffset(Field field);

  /**
   * Holds if the specified `Function` can be overridden in a derived class.
   */
  predicate isFunctionVirtual(Function f);
}
