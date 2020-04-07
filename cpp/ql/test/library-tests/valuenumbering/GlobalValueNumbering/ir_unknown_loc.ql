import cpp
import semmle.code.cpp.ir.internal.ASTValueNumbering

from Function f, ThisExpr known, ThisExpr unknown, boolean unknownFirst
where
  known.getEnclosingFunction() = f and
  unknown.getEnclosingFunction() = f and
  f.hasQualifiedName(_, "MidiDriver_ADLIB", "open") and
  not known.getLocation() instanceof UnknownLocation and
  unknown.getLocation() instanceof UnknownLocation and
  if known.getFile().getAbsolutePath() < unknown.getFile().getAbsolutePath()
  then unknownFirst = false
  else unknownFirst = true
select known, unknown, unknownFirst
