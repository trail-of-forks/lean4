module
import Lean
public meta import Lean
public section

set_option compiler.simplified true
set_option compiler.postponeCompile false
-- Deliberately conflicting settings: the profile must take precedence.
set_option compiler.reuse true
set_option compiler.extract_closed true

open Lean Compiler LCNF in
run_meta do
  let reference ← getPassManager
  let selected := reference.simplified
  unless reference.impurePasses.size == 14 && selected.impurePasses.size == 13 &&
      selected.basePasses.size == 18 && selected.monoPasses.size == 10 &&
      selected.monoPassesNoLambda.size == 8 do
    throwError "Unexpected conservative profile pass list"
  unless selected.impurePasses.any (·.name == `explicitBoxing) &&
      selected.impurePasses.any (·.name == `explicitRc) do
    throwError "Conservative profile must retain boxing and explicit reference counting"

open Lean Compiler LCNF in
@[cpass] meta def checkSimplifiedConfig : PassInstaller where
  phase := .base
  install passes := pure (passes.push {
    name := `checkSimplifiedConfig, phase := .base,
    run := fun decls => do
      let config ← getConfig
      unless compiler.simplified.get (← getOptions) && !config.resetReuse && !config.extractClosed do
        throwError "Simplified driver did not enforce its CompilerM configuration"
      return decls })

open Lean Compiler LCNF in
@[cpass] meta def checkNoCoalescing : PassInstaller where
  phase := .impure
  install passes := pure (passes.map fun pass =>
    if pass.name == `coalesceRc then { pass with run := fun _ =>
      throwError "RC coalescing ran under the simplified profile" }
    else pass)

@[noinline] def profileIdentity (x : UInt32) : UInt32 := x
@[noinline] def profileApply (f : UInt32 → UInt32) (x : UInt32) := f x

def main : IO Unit := do
  unless profileApply (fun x => profileIdentity (x + 1)) 4294967295 == 0 do
    throw (IO.userError "Simplified closure/UInt32 execution failed")
  IO.println "PASS simplified profile"

#eval main
