/-
Copyright (c) 2026 Samuel Moelius. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Moelius
-/
module

prelude
public import Lean.Compiler.LCNF.Basic
public import Lean.Compiler.LCNF.ScalarCAST
public import Lean.Compiler.NameMangling

public section
namespace Lean.Compiler.LCNF.ScalarC

/-- Evidence that an actual impure LCNF declaration belongs to the supported subset. -/
structure Input (decl : Decl .impure) where
  param : Param .impure
  params_eq : decl.params.toList = [param]
  result_type : decl.type = ImpureType.uint32
  param_type : param.type = ImpureType.uint32
  body_eq : decl.value = .code (.return param.fvarId)

private def checkUInt32 (type : Expr) : Except String (PLift (type = ImpureType.uint32)) :=
  match type with
  | .const name [] =>
    if hn : name = ``UInt32 then
      .ok ⟨congrArg (fun name => Expr.const name []) hn⟩
    else .error "scalar C: expected impure UInt32 type"
  | _ => .error "scalar C: expected impure UInt32 type"

def check (decl : Decl .impure) : Except String (Input decl) := do
  match hp : decl.params.toList with
  | [param] =>
    let ht ← checkUInt32 decl.type
    let hpt ← checkUInt32 param.type
    match hb : decl.value with
    | .code (.return r) =>
      if hr : r.name = param.fvarId.name then
        have hfid : r = param.fvarId := congrArg FVarId.mk hr
        return ⟨param, hp, ht.down, hpt.down, by simpa only [hfid] using hb⟩
      else throw "scalar C: return must refer to the sole parameter"
    | _ => throw "scalar C: only a single return instruction is supported"
  | _ => throw "scalar C: exactly one parameter is required"

/-- Operational semantics for the supported LCNF return instruction; other code is undefined here. -/
@[expose] def evalReturn {α : Type} (body : DeclValue .impure) (env : FVarId → α) : Option α :=
  match body with
  | .code (.return r) => some (env r)
  | _ => none

@[expose] def Input.lower (input : Input decl) (cName : String) : Function :=
  ⟨cName, input.param.binderName.mangle (pre := "v_")⟩

/-- Every accepted declaration preserves the return-instruction semantics. -/
theorem Input.correct (input : Input decl) (cName : String) (env : FVarId → α) :
    evalReturn decl.value env = some ((input.lower cName).eval (env input.param.fvarId)) := by
  rw [input.body_eq]
  rfl

end Lean.Compiler.LCNF.ScalarC
