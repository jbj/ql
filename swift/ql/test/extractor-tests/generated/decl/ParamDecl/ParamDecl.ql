// generated by codegen/codegen.py
import codeql.swift.elements
import TestUtils

from
  ParamDecl x, ModuleDecl getModule, int getNumberOfMembers, Type getInterfaceType,
  int getNumberOfAccessorDecls, string getName, Type getType, string hasAttachedPropertyWrapperType,
  string hasParentPattern, string hasParentInitializer, string hasPropertyWrapperBackingVarBinding,
  string hasPropertyWrapperBackingVar, string hasPropertyWrapperProjectionVarBinding,
  string hasPropertyWrapperProjectionVar, string isInout,
  string hasPropertyWrapperLocalWrappedVarBinding, string hasPropertyWrapperLocalWrappedVar
where
  toBeTested(x) and
  not x.isUnknown() and
  getModule = x.getModule() and
  getNumberOfMembers = x.getNumberOfMembers() and
  getInterfaceType = x.getInterfaceType() and
  getNumberOfAccessorDecls = x.getNumberOfAccessorDecls() and
  getName = x.getName() and
  getType = x.getType() and
  (
    if x.hasAttachedPropertyWrapperType()
    then hasAttachedPropertyWrapperType = "yes"
    else hasAttachedPropertyWrapperType = "no"
  ) and
  (if x.hasParentPattern() then hasParentPattern = "yes" else hasParentPattern = "no") and
  (if x.hasParentInitializer() then hasParentInitializer = "yes" else hasParentInitializer = "no") and
  (
    if x.hasPropertyWrapperBackingVarBinding()
    then hasPropertyWrapperBackingVarBinding = "yes"
    else hasPropertyWrapperBackingVarBinding = "no"
  ) and
  (
    if x.hasPropertyWrapperBackingVar()
    then hasPropertyWrapperBackingVar = "yes"
    else hasPropertyWrapperBackingVar = "no"
  ) and
  (
    if x.hasPropertyWrapperProjectionVarBinding()
    then hasPropertyWrapperProjectionVarBinding = "yes"
    else hasPropertyWrapperProjectionVarBinding = "no"
  ) and
  (
    if x.hasPropertyWrapperProjectionVar()
    then hasPropertyWrapperProjectionVar = "yes"
    else hasPropertyWrapperProjectionVar = "no"
  ) and
  (if x.isInout() then isInout = "yes" else isInout = "no") and
  (
    if x.hasPropertyWrapperLocalWrappedVarBinding()
    then hasPropertyWrapperLocalWrappedVarBinding = "yes"
    else hasPropertyWrapperLocalWrappedVarBinding = "no"
  ) and
  if x.hasPropertyWrapperLocalWrappedVar()
  then hasPropertyWrapperLocalWrappedVar = "yes"
  else hasPropertyWrapperLocalWrappedVar = "no"
select x, "getModule:", getModule, "getNumberOfMembers:", getNumberOfMembers, "getInterfaceType:",
  getInterfaceType, "getNumberOfAccessorDecls:", getNumberOfAccessorDecls, "getName:", getName,
  "getType:", getType, "hasAttachedPropertyWrapperType:", hasAttachedPropertyWrapperType,
  "hasParentPattern:", hasParentPattern, "hasParentInitializer:", hasParentInitializer,
  "hasPropertyWrapperBackingVarBinding:", hasPropertyWrapperBackingVarBinding,
  "hasPropertyWrapperBackingVar:", hasPropertyWrapperBackingVar,
  "hasPropertyWrapperProjectionVarBinding:", hasPropertyWrapperProjectionVarBinding,
  "hasPropertyWrapperProjectionVar:", hasPropertyWrapperProjectionVar, "isInout:", isInout,
  "hasPropertyWrapperLocalWrappedVarBinding:", hasPropertyWrapperLocalWrappedVarBinding,
  "hasPropertyWrapperLocalWrappedVar:", hasPropertyWrapperLocalWrappedVar
