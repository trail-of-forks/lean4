module
import Lean
import Lean.Compiler.LCNF.ScalarC
public meta import Lean
public meta import Lean.Compiler.LCNF.ScalarC

/-! Tests the checked UInt32 identity subset, rejection of other LCNF, and C byte agreement. -/

open Lean Compiler LCNF

private def parameter : Param .impure :=
  { fvarId := ⟨`x⟩, binderName := `x, type := ImpureType.uint32, borrow := false }

private def identityDecl : Decl .impure :=
  { name := `identity, levelParams := [], type := ImpureType.uint32,
    params := #[parameter], inlineAttr? := none, value := .code (.return parameter.fvarId) }

#guard (ScalarC.check identityDecl).isOk
#guard !(ScalarC.check { identityDecl with type := ImpureType.uint64 }).isOk
#guard !(ScalarC.check { identityDecl with params := #[{ parameter with type := ImpureType.uint64 }] }).isOk
#guard !(ScalarC.check { identityDecl with params := #[] }).isOk
#guard !(ScalarC.check { identityDecl with params := #[parameter, parameter] }).isOk
#guard !(ScalarC.check { identityDecl with value := .code (.return ⟨`other⟩) }).isOk
#guard !(ScalarC.check { identityDecl with value := .code (.unreach ImpureType.uint32) }).isOk

#guard ScalarC.render ⟨"f", "x"⟩ == "LEAN_EXPORT uint32_t f(uint32_t x){\n_start:\n{\nreturn x;\n}\n}\n"

example (f : ScalarC.Function) : ScalarC.render f = ScalarC.legacyText f.name f.parameter :=
  ScalarC.render_eq_legacyText f

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  for name in #[``ScalarC.Input.correct, ``ScalarC.render_bytes_eq_legacyText] do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"
