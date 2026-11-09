module
import Lean
public meta import Lean

open Lean Compiler LCNF

private meta def runnerProbe {α : Type} (action : CoreM α) (options : Options)
    (cancelTk? : Option IO.CancelToken := none) : CoreM (Except Exception (α × Core.State)) := do
  let env ← getEnv
  let context : Core.Context := {
    fileName := "<runner-probe>"
    fileMap := default
    options
    maxHeartbeats := 0
    cancelTk?
  }
  (action.run context { env }).toBaseIO

run_meta do
  let options := ({} : Options).setBool `trace.Compiler true
    |>.setBool `trace.Compiler.init true |>.setBool `trace.Compiler.stat true
  let phases ← IO.mkRef (#[] : Array Phase)
  let passes : Array Pass := #[
    { name := `first, phase := .base, phaseOut := .mono, run := fun ds => do
        let phase ← getPhase; phases.modify (·.push phase); return ds },
    { name := `second, phase := .mono, phaseOut := .impure, run := fun _ => do
        let phase ← getPhase; phases.modify (·.push phase); return #[] },
    { name := `third, phase := .impure, run := fun ds => do
        let phase ← getPhase; phases.modify (·.push phase); return ds }]
  let .ok (result, state) ← runnerProbe
      (CompilerM.run (PassManager.runPassManagerPartPlain .pure .impure passes #[] true)) options
    | throwError "Plain runner did not complete phase transitions"
  unless result.isEmpty && (← phases.get) == #[.base, .mono, .impure] && state.traceState.traces.isEmpty do
    throwError "Plain runner changed order, phases, or emitted runner traces"

  -- The same harmless pass produces diagnostic nodes when explicitly requested.
  let .ok (_, state) ← runnerProbe
      (CompilerM.run (PassManager.runPassManagerPartDiagnostic .pure .pure "probe"
        #[{ name := `init, phase := .base, run := pure }] #[] false)) options
    | throwError "Diagnostic runner failed"
  unless !state.traceState.traces.isEmpty do
    throwError "Diagnostic control did not produce a trace"

  -- A malformed declaration is accepted only when both check switches are off.
  -- This also tests that enabled trace/pretty-print flags do not inspect it in plain mode.
  let bad : Decl .pure := { (default : Decl .pure) with
    name := `runnerProbeBad
    type := .const ``UInt32 []
    value := .code (.return ⟨`outOfScope⟩)
  }
  for enabled in #[false, true] do
    for always in #[false, true] do
      let pass : Pass := { name := `init, phase := .base, shouldAlwaysRunCheck := always, run := pure }
      let outcome ← runnerProbe
        (CompilerM.run (PassManager.runPassManagerPartPlain .pure .pure #[pass] #[bad] enabled)) options
      match outcome with
      | .ok (_, state) =>
        unless !enabled && !always && state.traceState.traces.isEmpty do
          throwError "Plain runner skipped a requested/mandatory check or emitted diagnostics"
      | .error _ =>
        unless enabled || always do
          throwError "Plain runner checked/pretty-printed unchecked data"

  -- Cancellation is observed before entering the pass body.
  let token ← IO.CancelToken.new
  token.set
  let ran ← IO.mkRef false
  let outcome ← runnerProbe
    (CompilerM.run (PassManager.runPassManagerPartPlain .pure .pure
      #[{ name := `cancelProbe, phase := .base, run := fun ds => do ran.set true; return ds }] #[] false))
    options (some token)
  match outcome with
  | .error error =>
    unless error.isInterrupt && !(← ran.get) do
      throwError "Plain runner did not preserve cancellation before the pass"
  | .ok _ => throwError "Plain runner ignored cancellation"
  logInfo "PASS plain runner: order, phases, checks, cancellation, and diagnostic separation"
