module
import Lean
import Lean.Compiler.LCNF.ScalarC
public meta import Lean
public meta import Lean.Compiler.LCNF.ScalarC

/-! Compile Lean source to impure LCNF and compare the structured and original textual C paths. -/

set_option compiler.postponeCompile false

@[noinline] def scalarIdentity (x : UInt32) : UInt32 := x
@[noinline] def scalarUnicodeIdentity (χ : UInt32) : UInt32 := χ

open Lean Compiler LCNF in
run_meta do
  for name in #[``scalarIdentity, ``scalarUnicodeIdentity] do
    let names := #[name]
    let old ← emitCForDeclsOriginal (← getMainModule) names
    let current ← emitCForDecls (← getMainModule) names
    let new ← ScalarC.emitCForDecls (← getMainModule) names
    unless old.toUTF8 == new.toUTF8 && current.toUTF8 == new.toUTF8 do
      throwError "structured backend differs from original C output for {name}"

@[noinline] def scalarUInt64Identity (x : UInt64) : UInt64 := x
@[noinline] def scalarAdd (x : UInt32) : UInt32 := x + 1

open Lean Compiler LCNF in
run_meta do
  for name in #[``scalarUInt64Identity, ``scalarAdd] do
    let names := #[name]
    let old ← emitCForDeclsOriginal (← getMainModule) names
    let current ← emitCForDecls (← getMainModule) names
    unless old.toUTF8 == current.toUTF8 do
      throwError "fallback changed original output for {name}"
    let rejected ← try
      let _ ← ScalarC.emitCForDecls (← getMainModule) names
      pure false
    catch _ => pure true
    unless rejected do throwError "structured backend accepted unsupported {name}"
