private import cpp
private import semmle.code.cpp.ir.internal.IRUtilities
private import semmle.code.cpp.ir.implementation.internal.OperandTag
private import semmle.code.cpp.ir.internal.CppType
private import semmle.code.cpp.ir.internal.TempVariableTag
private import InstructionTag
private import TranslatedCondition
private import TranslatedDeclarationEntry
private import TranslatedElement
private import TranslatedExpr
private import TranslatedFunction
private import TranslatedInitialization

TranslatedStmt getTranslatedStmt(Stmt stmt) { result.getAST() = stmt }

abstract class TranslatedStmt extends TranslatedElement, TTranslatedStmt {
  Stmt stmt;

  TranslatedStmt() { this = TTranslatedStmt(stmt) }

  final override string toString() { result = stmt.toString() }

  final override Locatable getAST() { result = stmt }

  final override Function getFunction() { result = stmt.getEnclosingFunction() }
}

class TranslatedEmptyStmt extends TranslatedStmt {
  TranslatedEmptyStmt() {
    stmt instanceof EmptyStmt or
    stmt instanceof LabelStmt or
    stmt instanceof SwitchCase
  }

  override TranslatedElement getChild(int id) { none() }

  override InstructionDesc getFirstInstructionDesc() { result = SelfInstruction(OnlyInstructionTag()) }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    tag = OnlyInstructionTag() and
    opcode instanceof Opcode::NoOp and
    resultType = getVoidType()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    result = getParent().getChildSuccessor(this) and
    kind instanceof GotoEdge
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) { none() }
}

/**
 * The IR translation of a declaration statement. This consists of the IR for each of the individual
 * local variables declared by the statement. Declarations for extern variables and functions
 * do not generate any instructions.
 */
class TranslatedDeclStmt extends TranslatedStmt {
  override DeclStmt stmt;

  override TranslatedElement getChild(int id) { result = getDeclarationEntry(id) }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    none()
  }

  override InstructionDesc getFirstInstructionDesc() {
    result = FirstInstruction(getDeclarationEntry(0))
    or
    not exists(getDeclarationEntry(0)) and result = SelfSuccessorInstruction()
  }

  private int getChildCount() { result = count(getDeclarationEntry(_)) }

  /**
   * Gets the `TranslatedDeclarationEntry` child at zero-based index `index`. Since not all
   * `DeclarationEntry` objects have a `TranslatedDeclarationEntry` (e.g. extern functions), we map
   * the original children into a contiguous range containing only those with an actual
   * `TranslatedDeclarationEntry`.
   */
  private TranslatedDeclarationEntry getDeclarationEntry(int index) {
    result =
      rank[index + 1](TranslatedDeclarationEntry entry, int originalIndex |
        entry = getTranslatedDeclarationEntry(stmt.getDeclarationEntry(originalIndex))
      |
        entry order by originalIndex
      )
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    exists(int index |
      child = getDeclarationEntry(index) and
      if index = (getChildCount() - 1)
      then result = SelfSuccessorInstruction()
      else result = FirstInstruction(getDeclarationEntry(index + 1))
    )
  }
}

class TranslatedExprStmt extends TranslatedStmt {
  override ExprStmt stmt;

  TranslatedExpr getExpr() {
    result = getTranslatedExpr(stmt.(ExprStmt).getExpr().getFullyConverted())
  }

  override TranslatedElement getChild(int id) { id = 0 and result = getExpr() }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    none()
  }

  override InstructionDesc getFirstInstructionDesc() { result = FirstInstruction(getExpr()) }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    child = getExpr() and
    result = SelfSuccessorInstruction()
  }
}

abstract class TranslatedReturnStmt extends TranslatedStmt {
  override ReturnStmt stmt;

  final TranslatedFunction getEnclosingFunction() {
    result = getTranslatedFunction(stmt.getEnclosingFunction())
  }
}

class TranslatedReturnValueStmt extends TranslatedReturnStmt, TranslatedVariableInitialization {
  TranslatedReturnValueStmt() { stmt.hasExpr() }

  final override InstructionDesc getInitializationSuccessorDesc() {
    result = getEnclosingFunction().getReturnSuccessorInstructionDesc()
  }

  final override Type getTargetType() { result = getEnclosingFunction().getReturnType() }

  final override TranslatedInitialization getInitialization() {
    result = getTranslatedInitialization(stmt.getExpr().getFullyConverted())
  }

  final override IRVariable getIRVariable() { result = getEnclosingFunction().getReturnVariable() }
}

class TranslatedReturnVoidStmt extends TranslatedReturnStmt {
  TranslatedReturnVoidStmt() { not stmt.hasExpr() }

  override TranslatedElement getChild(int id) { none() }

  override InstructionDesc getFirstInstructionDesc() { result = SelfInstruction(OnlyInstructionTag()) }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    tag = OnlyInstructionTag() and
    opcode instanceof Opcode::NoOp and
    resultType = getVoidType()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    result = getEnclosingFunction().getReturnSuccessorInstruction() and
    kind instanceof GotoEdge
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) { none() }
}

/**
 * The IR translation of a C++ `try` statement.
 */
class TranslatedTryStmt extends TranslatedStmt {
  override TryStmt stmt;

  override TranslatedElement getChild(int id) {
    id = 0 and result = getBody()
    or
    result = getHandler(id - 1)
  }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    none()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override InstructionDesc getFirstInstructionDesc() { result = FirstInstruction(getBody()) }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    // All children go to the successor of the `try`.
    child = getAChild() and result = SelfSuccessorInstruction()
  }

  final Instruction getNextHandler(TranslatedHandler handler) {
    exists(int index |
      handler = getHandler(index) and
      result = getHandler(index + 1).getFirstInstruction()
    )
    or
    // The last catch clause flows to the exception successor of the parent
    // of the `try`, because the exception successor of the `try` itself is
    // the first catch clause.
    handler = getHandler(stmt.getNumberOfCatchClauses() - 1) and
    result = getParent().getExceptionSuccessorInstruction()
  }

  final override Instruction getExceptionSuccessorInstruction() {
    result = getHandler(0).getFirstInstruction()
  }

  private TranslatedHandler getHandler(int index) {
    result = getTranslatedStmt(stmt.getChild(index + 1))
  }

  private TranslatedStmt getBody() { result = getTranslatedStmt(stmt.getStmt()) }
}

class TranslatedBlock extends TranslatedStmt {
  override Block stmt;

  override TranslatedElement getChild(int id) { result = getStmt(id) }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    isEmpty() and
    opcode instanceof Opcode::NoOp and
    tag = OnlyInstructionTag() and
    resultType = getVoidType()
  }

  override InstructionDesc getFirstInstructionDesc() {
    if isEmpty()
    then result = SelfInstruction(OnlyInstructionTag())
    else result = FirstInstruction(getStmt(0))
  }

  private predicate isEmpty() { not exists(stmt.getStmt(0)) }

  private TranslatedStmt getStmt(int index) { result = getTranslatedStmt(stmt.getStmt(index)) }

  private int getStmtCount() { result = stmt.getNumStmt() }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    result = getParent().getChildSuccessor(this) and
    kind instanceof GotoEdge
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    exists(int index |
      child = getStmt(index) and
      if index = (getStmtCount() - 1)
      then result = SelfSuccessorInstruction()
      else result = FirstInstruction(getStmt(index + 1))
    )
  }
}

/**
 * The IR translation of a C++ `catch` handler.
 */
abstract class TranslatedHandler extends TranslatedStmt {
  override Handler stmt;

  override TranslatedElement getChild(int id) { id = 1 and result = getBlock() }

  override InstructionDesc getFirstInstructionDesc() { result = SelfInstruction(CatchTag()) }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    child = getBlock() and result = SelfSuccessorInstruction()
  }

  override Instruction getExceptionSuccessorInstruction() {
    // A throw from within a `catch` block flows to the handler for the parent of
    // the `try`.
    result = getParent().getParent().getExceptionSuccessorInstruction()
  }

  TranslatedStmt getBlock() { result = getTranslatedStmt(stmt.getBlock()) }
}

/**
 * The IR translation of a C++ `catch` block that catches an exception with a
 * specific type (e.g. `catch (const std::exception&)`).
 */
class TranslatedCatchByTypeHandler extends TranslatedHandler {
  TranslatedCatchByTypeHandler() { exists(stmt.getParameter()) }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    tag = CatchTag() and
    opcode instanceof Opcode::CatchByType and
    resultType = getVoidType()
  }

  override TranslatedElement getChild(int id) {
    result = super.getChild(id)
    or
    id = 0 and result = getParameter()
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    result = super.getChildSuccessorDesc(child)
    or
    child = getParameter() and result = FirstInstruction(getBlock())
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = CatchTag() and
    (
      kind instanceof GotoEdge and
      result = getParameter().getFirstInstruction()
      or
      kind instanceof ExceptionEdge and
      result = getParent().(TranslatedTryStmt).getNextHandler(this)
    )
  }

  override CppType getInstructionExceptionType(InstructionTag tag) {
    tag = CatchTag() and
    result = getTypeForPRValue(stmt.getParameter().getType())
  }

  private TranslatedParameter getParameter() {
    result = getTranslatedParameter(stmt.getParameter())
  }
}

/**
 * The IR translation of a C++ `catch (...)` block.
 */
class TranslatedCatchAnyHandler extends TranslatedHandler {
  TranslatedCatchAnyHandler() { not exists(stmt.getParameter()) }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    tag = CatchTag() and
    opcode instanceof Opcode::CatchAny and
    resultType = getVoidType()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = CatchTag() and
    kind instanceof GotoEdge and
    result = getBlock().getFirstInstruction()
  }
}

class TranslatedIfStmt extends TranslatedStmt, ConditionContext {
  override IfStmt stmt;

  override InstructionDesc getFirstInstructionDesc() { result = FirstInstruction(getCondition()) }

  override TranslatedElement getChild(int id) {
    id = 0 and result = getCondition()
    or
    id = 1 and result = getThen()
    or
    id = 2 and result = getElse()
  }

  private TranslatedCondition getCondition() {
    result = getTranslatedCondition(stmt.getCondition().getFullyConverted())
  }

  private TranslatedStmt getThen() { result = getTranslatedStmt(stmt.getThen()) }

  private TranslatedStmt getElse() { result = getTranslatedStmt(stmt.getElse()) }

  private predicate hasElse() { exists(stmt.getElse()) }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getChildTrueSuccessor(TranslatedCondition child) {
    child = getCondition() and
    result = getThen().getFirstInstruction()
  }

  override Instruction getChildFalseSuccessor(TranslatedCondition child) {
    child = getCondition() and
    if hasElse()
    then result = getElse().getFirstInstruction()
    else result = getParent().getChildSuccessor(this)
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    (child = getThen() or child = getElse()) and
    result = SelfSuccessorInstruction()
  }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    none()
  }
}

abstract class TranslatedLoop extends TranslatedStmt, ConditionContext {
  override Loop stmt;

  final TranslatedCondition getCondition() {
    result = getTranslatedCondition(stmt.getCondition().getFullyConverted())
  }

  final TranslatedStmt getBody() { result = getTranslatedStmt(stmt.getStmt()) }

  final InstructionDesc getFirstConditionInstructionDesc() {
    result = FirstInstruction(getFirstConditionChild())
  }

  final Instruction getFirstConditionInstruction() {
    result = getFirstConditionChild().getFirstInstruction()
  }

  final TranslatedElement getFirstConditionChild() {
    if hasCondition()
    then result = getCondition()
    else result = getBody()
  }

  final predicate hasCondition() { exists(stmt.getCondition()) }

  override TranslatedElement getChild(int id) {
    id = 0 and result = getCondition()
    or
    id = 1 and result = getBody()
  }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    none()
  }

  final override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  final override Instruction getChildTrueSuccessor(TranslatedCondition child) {
    child = getCondition() and result = getBody().getFirstInstruction()
  }

  final override Instruction getChildFalseSuccessor(TranslatedCondition child) {
    child = getCondition() and result = getParent().getChildSuccessor(this)
  }
}

class TranslatedWhileStmt extends TranslatedLoop {
  TranslatedWhileStmt() { stmt instanceof WhileStmt }

  override InstructionDesc getFirstInstructionDesc() { result = getFirstConditionInstructionDesc() }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    child = getBody() and result = getFirstConditionInstructionDesc()
  }
}

class TranslatedDoStmt extends TranslatedLoop {
  TranslatedDoStmt() { stmt instanceof DoStmt }

  override InstructionDesc getFirstInstructionDesc() { result = FirstInstruction(getBody()) }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    child = getBody() and result = getFirstConditionInstructionDesc()
  }
}

class TranslatedForStmt extends TranslatedLoop {
  override ForStmt stmt;

  override TranslatedElement getChild(int id) {
    id = 0 and result = getInitialization()
    or
    id = 1 and result = getCondition()
    or
    id = 2 and result = getUpdate()
    or
    id = 3 and result = getBody()
  }

  private TranslatedStmt getInitialization() {
    result = getTranslatedStmt(stmt.getInitialization())
  }

  private predicate hasInitialization() { exists(stmt.getInitialization()) }

  TranslatedExpr getUpdate() { result = getTranslatedExpr(stmt.getUpdate().getFullyConverted()) }

  private predicate hasUpdate() { exists(stmt.getUpdate()) }

  override InstructionDesc getFirstInstructionDesc() {
    if hasInitialization()
    then result = FirstInstruction(getInitialization())
    else result = getFirstConditionInstructionDesc()
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    child = getInitialization() and
    result = getFirstConditionInstructionDesc()
    or
    (
      child = getBody() and
      if hasUpdate()
      then result = FirstInstruction(getUpdate())
      else result = getFirstConditionInstructionDesc()
    )
    or
    child = getUpdate() and result = getFirstConditionInstructionDesc()
  }
}

/**
 * The IR translation of a range-based `for` loop.
 * Note that this class does not extend `TranslatedLoop`. This is because the "body" of the
 * range-based `for` loop consists of the per-iteration variable declaration followed by the
 * user-written body statement. It is easier to handle the control flow of the loop separately,
 * rather than synthesizing a single body or complicating the interface of `TranslatedLoop`.
 */
class TranslatedRangeBasedForStmt extends TranslatedStmt, ConditionContext {
  override RangeBasedForStmt stmt;

  override TranslatedElement getChild(int id) {
    id = 0 and result = getRangeVariableDeclaration()
    or
    id = 1 and result = getBeginVariableDeclaration()
    or
    id = 2 and result = getEndVariableDeclaration()
    or
    id = 3 and result = getCondition()
    or
    id = 4 and result = getUpdate()
    or
    id = 5 and result = getVariableDeclaration()
    or
    id = 6 and result = getBody()
  }

  override InstructionDesc getFirstInstructionDesc() {
    result = FirstInstruction(getRangeVariableDeclaration())
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    child = getRangeVariableDeclaration() and
    result = FirstInstruction(getBeginVariableDeclaration())
    or
    child = getBeginVariableDeclaration() and
    result = FirstInstruction(getEndVariableDeclaration())
    or
    child = getEndVariableDeclaration() and
    result = FirstInstruction(getCondition())
    or
    child = getVariableDeclaration() and
    result = FirstInstruction(getBody())
    or
    child = getBody() and
    result = FirstInstruction(getUpdate())
    or
    child = getUpdate() and
    result = FirstInstruction(getCondition())
  }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    none()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) { none() }

  override Instruction getChildTrueSuccessor(TranslatedCondition child) {
    child = getCondition() and result = getVariableDeclaration().getFirstInstruction()
  }

  override Instruction getChildFalseSuccessor(TranslatedCondition child) {
    child = getCondition() and result = getParent().getChildSuccessor(this)
  }

  private TranslatedRangeBasedForVariableDeclaration getRangeVariableDeclaration() {
    result = getTranslatedRangeBasedForVariableDeclaration(stmt.getRangeVariable())
  }

  private TranslatedRangeBasedForVariableDeclaration getBeginVariableDeclaration() {
    result = getTranslatedRangeBasedForVariableDeclaration(stmt.getBeginVariable())
  }

  private TranslatedRangeBasedForVariableDeclaration getEndVariableDeclaration() {
    result = getTranslatedRangeBasedForVariableDeclaration(stmt.getEndVariable())
  }

  // Public for getInstructionBackEdgeSuccessor
  final TranslatedCondition getCondition() {
    result = getTranslatedCondition(stmt.getCondition().getFullyConverted())
  }

  // Public for getInstructionBackEdgeSuccessor
  final TranslatedExpr getUpdate() {
    result = getTranslatedExpr(stmt.getUpdate().getFullyConverted())
  }

  private TranslatedRangeBasedForVariableDeclaration getVariableDeclaration() {
    result = getTranslatedRangeBasedForVariableDeclaration(stmt.getVariable())
  }

  private TranslatedStmt getBody() { result = getTranslatedStmt(stmt.getStmt()) }
}

class TranslatedJumpStmt extends TranslatedStmt {
  override JumpStmt stmt;

  override InstructionDesc getFirstInstructionDesc() { result = SelfInstruction(OnlyInstructionTag()) }

  override TranslatedElement getChild(int id) { none() }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    tag = OnlyInstructionTag() and
    opcode instanceof Opcode::NoOp and
    resultType = getVoidType()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = OnlyInstructionTag() and
    kind instanceof GotoEdge and
    result = getTranslatedStmt(stmt.getTarget()).getFirstInstruction()
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) { none() }
}

private EdgeKind getCaseEdge(SwitchCase switchCase) {
  exists(CaseEdge edge |
    result = edge and
    hasCaseEdge(switchCase, edge.getMinValue(), edge.getMaxValue())
  )
  or
  switchCase instanceof DefaultCase and result instanceof DefaultEdge
}

class TranslatedSwitchStmt extends TranslatedStmt {
  override SwitchStmt stmt;

  private TranslatedExpr getExpr() {
    result = getTranslatedExpr(stmt.getExpr().getFullyConverted())
  }

  private TranslatedStmt getBody() { result = getTranslatedStmt(stmt.getStmt()) }

  override InstructionDesc getFirstInstructionDesc() { result = FirstInstruction(getExpr()) }

  override TranslatedElement getChild(int id) {
    id = 0 and result = getExpr()
    or
    id = 1 and result = getBody()
  }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    tag = SwitchBranchTag() and
    opcode instanceof Opcode::Switch and
    resultType = getVoidType()
  }

  override Instruction getInstructionOperand(InstructionTag tag, OperandTag operandTag) {
    tag = SwitchBranchTag() and
    operandTag instanceof ConditionOperandTag and
    result = getExpr().getResult()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = SwitchBranchTag() and
    exists(SwitchCase switchCase |
      switchCase = stmt.getASwitchCase() and
      kind = getCaseEdge(switchCase) and
      result = getTranslatedStmt(switchCase).getFirstInstruction()
    )
    or
    not stmt.hasDefaultCase() and
    tag = SwitchBranchTag() and
    kind instanceof DefaultEdge and
    result = getParent().getChildSuccessor(this)
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    child = getExpr() and result = SelfInstruction(SwitchBranchTag())
    or
    child = getBody() and result = SelfSuccessorInstruction()
  }
}

class TranslatedAsmStmt extends TranslatedStmt {
  override AsmStmt stmt;

  override TranslatedExpr getChild(int id) {
    result = getTranslatedExpr(stmt.getChild(id).(Expr).getFullyConverted())
  }

  override InstructionDesc getFirstInstructionDesc() {
    if exists(getChild(0))
    then result = FirstInstruction(getChild(0))
    else result = SelfInstruction(AsmTag())
  }

  override predicate hasInstruction(Opcode opcode, InstructionTag tag, CppType resultType) {
    tag = AsmTag() and
    opcode instanceof Opcode::InlineAsm and
    resultType = getUnknownType()
  }

  override Instruction getInstructionOperand(InstructionTag tag, OperandTag operandTag) {
    tag = AsmTag() and
    operandTag instanceof SideEffectOperandTag and
    result = getTranslatedFunction(stmt.getEnclosingFunction()).getUnmodeledDefinitionInstruction()
    or
    exists(int index |
      tag = AsmTag() and
      operandTag = asmOperand(index) and
      result = getChild(index).getResult()
    )
  }

  final override CppType getInstructionOperandType(InstructionTag tag, TypedOperandTag operandTag) {
    tag = AsmTag() and
    operandTag instanceof SideEffectOperandTag and
    result = getUnknownType()
  }

  override Instruction getInstructionSuccessor(InstructionTag tag, EdgeKind kind) {
    tag = AsmTag() and
    result = getParent().getChildSuccessor(this) and
    kind instanceof GotoEdge
  }

  override InstructionDesc getChildSuccessorDesc(TranslatedElement child) {
    exists(int index |
      child = getChild(index) and
      if exists(getChild(index + 1))
      then result = FirstInstruction(getChild(index + 1))
      else result = SelfInstruction(AsmTag())
    )
  }
}
