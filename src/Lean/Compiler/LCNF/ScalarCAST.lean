/-
Copyright (c) 2026 Samuel Moelius. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Moelius
-/
module

prelude
public import Init

public section

namespace Lean.Compiler.LCNF.ScalarC

/-- A C AST restricted to `uint32_t name(uint32_t parameter) { return parameter; }`.
The printer includes the labels and blocks used by Lean's existing C emitter. -/
structure Function where
  name : String
  parameter : String
  deriving Repr, BEq

/-- The return-parameter fragment has the same semantics for any value domain. -/
@[expose] def Function.eval {α : Type} (_ : Function) (argument : α) : α := argument

@[expose] def cType : String := "uint32_t"

@[expose] def renderReturn (f : Function) : String := "return " ++ f.parameter ++ ";\n"

@[expose] def render (f : Function) : String :=
  "LEAN_EXPORT " ++ cType ++ " " ++ f.name ++ "(" ++ cType ++ " " ++ f.parameter ++
    "){\n_start:\n{\n" ++ renderReturn f ++ "}\n}\n"

/-- The total textual path factored out of the existing emitter for this subset. -/
@[expose] def legacyText (name parameter : String) : String :=
  "LEAN_EXPORT " ++ "uint32_t" ++ " " ++ name ++ "(" ++ "uint32_t" ++ " " ++ parameter ++
    "){\n_start:\n{\n" ++ ("return " ++ parameter ++ ";\n") ++ "}\n}\n"

/-- Equality is of the complete emitted function text, including whitespace. -/
theorem render_eq_legacyText (f : Function) : render f = legacyText f.name f.parameter := rfl

/-- Byte-for-byte equality, including line endings. -/
theorem render_bytes_eq_legacyText (f : Function) :
    (render f).toUTF8 = (legacyText f.name f.parameter).toUTF8 :=
  congrArg String.toUTF8 (render_eq_legacyText f)

end Lean.Compiler.LCNF.ScalarC
