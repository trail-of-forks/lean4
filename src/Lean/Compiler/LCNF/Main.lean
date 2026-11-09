/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Compiler.Options
import Lean.Compiler.IR
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.LCNF.Check
import Lean.Meta.Match.MatcherInfo
import Lean.Compiler.LCNF.SplitSCC
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager

public section
namespace Lean.Compiler.LCNF

/-- Select the conservative proof-facing profile for automatic compilation. -/
register_builtin_option compiler.simplified : Bool := {
  defValue := false
  descr := "use the conservative LCNF profile: disable closed extraction and reset/reuse, and omit RC coalescing"
}

/-- Restore diagnostic wrappers while using the conservative pass selection. -/
register_builtin_option compiler.simplified.diagnostics : Bool := {
  defValue := false
  descr := "use the diagnostic runner with the conservative compiler profile"
}

/-- Enforce the profile even if a caller requested either optimization. Keep the
profile flag in base options so dependency resumption uses the same pipeline. -/
def simplifiedOptions (opts : Options) : Options :=
  compiler.reuse.set (compiler.extract_closed.set (compiler.simplified.set opts true) false) false

/-- Fix the runner policy as well as the pass profile for resumed dependencies. -/
def simplifiedRunnerOptions (diagnostics : Bool) (opts : Options) : Options :=
  compiler.simplified.diagnostics.set (simplifiedOptions opts) diagnostics

/--
We do not generate code for `declName` if
- Its type is a proposition.
- Its type is a type former.
- It is tagged as `[macro_inline]`.
- It is a type class instance.

Remark: we still generate code for declarations tagged as `[inline]`
and `[specialize]` since they can be partially applied.
-/
def shouldGenerateCode (declName : Name) : CoreM Bool := do
  if (← isCompIrrelevant |>.run') then return false
  let env ← getEnv
  if isExtern env declName then return true
  -- Look up the decl in the kernel environment, since it will appear there
  -- as an axiom (rather than a definition) in the case of a kernel error.
  let some info := env.constants.find? declName | return false
  unless info.hasValue (allowOpaque := true) do return false
  if hasMacroInlineAttribute env declName then return false
  if (getImplementedBy? env declName).isSome then return false
  if (← Meta.isMatcher declName) then return false
  if (← Meta.isMatcherLike declName) then return false
  if isCasesOnLike env declName then return false
  -- TODO: check if type class instance
  return true
where
  isCompIrrelevant : MetaM Bool := do
    let info ← getConstInfo declName
    Meta.isProp info.type <||> Meta.isTypeFormerType info.type

/--
A checkpoint in code generation to print all declarations in between
compiler passes in order to ease debugging.
The trace can be viewed with `set_option trace.Compiler.step true`.
-/
def checkpoint (stepName : Name) (decls : Array (Decl pu)) (shouldCheck : Bool) : CompilerM Unit := do
  for decl in decls do
    trace[Compiler.stat] "{decl.name} : {decl.size}"
    withOptions (fun opts => opts.set `pp.motives.pi false) do
      let clsName := `Compiler ++ stepName
      if (← Lean.isTracingEnabledFor clsName) then
        if compiler.traceUnnormalized.get (← getOptions) then
          Lean.addTrace clsName m!"size: {decl.size}\n{← ppDecl decl}"
        else
          Lean.addTrace clsName m!"size: {decl.size}\n{← ppDecl' decl (← getPhase)}"
      if shouldCheck then
        decl.check

def isValidMainType (type : Expr) : Bool :=
  let isValidResultName (name : Name) : Bool :=
    name == ``UInt32 || name == ``Unit || name == ``PUnit
  match type with
  | .forallE _ d b _ =>
    match d, b with
    | .app (.const ``List _) (.const ``String _), .app (.const ``IO _) (.const resultName _) =>
      isValidResultName resultName
    | _, _ => false
  | .app (.const ``IO _) (.const resultName _) =>
    isValidResultName resultName
  | _ => false

/-- A postponed call of `compileDecls`. -/
structure PostponedCompileDecls where
  /-- Declaration names of this mutual group. -/
  declNames : Array Name
  /-- Options at time of original call, to be restored for tracing etc. -/
  options : Options
deriving BEq

/--
Saves postponed `compileDecls` calls.

We use this state both in `lean` when doing post-hoc compilation of non-meta declarations on `#eval`
etc. as well as in `leanir` to do separate compilation of all defs.
-/
builtin_initialize postponedCompileDeclsExt : SimplePersistentEnvExtension PostponedCompileDecls (NameMap PostponedCompileDecls) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn    := fun s e => e.declNames.foldl (·.insert · e) s
    toArrayFn     := fun es => es.toArray
    asyncMode     := .sync
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter
      (fun s e => !e.declNames.any s.contains) (fun s e => e.declNames.foldl (·.insert · e) s)
    exportEntriesFnEx? := some fun _ _ es =>
      -- `leanir` imports the target module privately
      { exported := #[], server := #[], «private» := es.toArray }
  }

def resumeCompilation (declName : Name) (baseOpts : Options) : CoreM Unit := do
  let some decls := postponedCompileDeclsExt.getState (← getEnv) |>.find? declName | return
  let opts := baseOpts.mergeBy (fun _ base _ => base) decls.options
  let opts := compiler.postponeCompile.set opts false
  modifyEnv (postponedCompileDeclsExt.modifyState · fun s => decls.declNames.foldl (·.erase) s)
  -- NOTE: we *must* throw away the current options as they could depend on the specific recursion
  -- we did to get here.
  withOptions (fun _ => opts) do
  Core.prependError m!"Failed to compile `{declName}`" do
    (← compileDeclsRef.get) decls.declNames baseOpts

namespace PassManager

/-- Preserve all registered passes except RC coalescing. In particular boxing,
explicit RC, phase saves and user-installed passes with other names remain. -/
def simplified (manager : PassManager) : PassManager :=
  { manager with impurePasses := manager.impurePasses.filter (fun pass => pass.name != `coalesceRc) }

def runPassManagerPartDiagnostic (inPhase outPhase : Purity) (profilerName : String)
    (passes : Array Pass) (decls : Array (Decl inPhase)) (isCheckEnabled : Bool) :
    CompilerM (Array (Decl outPhase)) := do
  profileitM Exception profilerName (← getOptions) do
    let mut state : (pu : Purity) × Array (Decl pu) := ⟨inPhase, decls⟩
    for pass in passes do
      checkSystem "LCNF compiler"
      state ← withTraceNode `Compiler (fun _ => return m!"compiler phase: {pass.phase}, pass: {pass.name}") do
        let decls ← withPhase pass.phase do
          state.fst.withAssertPurity pass.phase.toPurity fun h => do
            pass.run (h ▸ state.snd)
        pure ⟨_, decls⟩
      withPhase pass.phaseOut <| checkpoint pass.name state.snd (isCheckEnabled || pass.shouldAlwaysRunCheck)
    let decls := state.fst.withAssertPurity outPhase fun h => h ▸ state.snd
    return decls

/-- Finite phase runner without optional trace/profiler/pretty-printing wrappers.
Resource checks, phase scopes, dynamic purity assertions and all requested or
mandatory declaration checks are retained. Individual passes are unchanged. -/
def runPassManagerPartPlain (inPhase outPhase : Purity)
    (passes : Array Pass) (decls : Array (Decl inPhase)) (isCheckEnabled : Bool) :
    CompilerM (Array (Decl outPhase)) := do
  let mut state : (pu : Purity) × Array (Decl pu) := ⟨inPhase, decls⟩
  for pass in passes do
    checkSystem "LCNF compiler"
    let decls ← withPhase pass.phase do
      state.fst.withAssertPurity pass.phase.toPurity fun h => do
        pass.run (h ▸ state.snd)
    state := ⟨_, decls⟩
    withPhase pass.phaseOut do
      if isCheckEnabled || pass.shouldAlwaysRunCheck then
        for decl in state.snd do
          decl.check
  return state.fst.withAssertPurity outPhase fun h => h ▸ state.snd

/-- Strategies for the driver's optional diagnostic boundaries. They share the
same preparation, passes, state saves, checks and IR implementation. -/
structure DriverRunner where
  runPart : (inPhase outPhase : Purity) → String → Array Pass →
    Array (Decl inPhase) → Bool → CompilerM (Array (Decl outPhase))
  split : Array (Decl .pure) → CompilerM (Array (Array (Decl .pure)))
  finish : Array (Decl .impure) → CompilerM Unit
  implementedBy : Name → Name → CompilerM Unit
  postponed : Array Name → CompilerM Unit

/-- The diagnostic strategy retains the reference driver's wrappers. -/
def diagnosticRunner : DriverRunner where
  runPart := runPassManagerPartDiagnostic
  split decls := withTraceNode `Compiler.splitSCC (fun _ => return m!"Splitting up SCC") do
    splitScc decls
  finish decls := do
    if (← Lean.isTracingEnabledFor `Compiler.result) then
      for decl in decls do
        let decl ← normalizeFVarIds decl
        Lean.addTrace `Compiler.result m!"size: {decl.size}\n{← ppDecl' decl (← getPhase)}"
    profileitM Exception "compilation (IR)" (← getOptions) do
      let irDecls ← IR.toIR decls
      discard <| IR.compile irDecls
  implementedBy fnName declName := do
    trace[Compiler.inferVisibility] m!"Marking {fnName} as opaque because it implements {declName}"
  postponed names := do trace[Compiler] "postponing compilation of {names}"

/-- No optional diagnostic callbacks in the driver strategy. Existing workers
can still have their own diagnostics; their implementations are not rewritten. -/
def plainRunner : DriverRunner where
  runPart := fun inPhase outPhase _ => runPassManagerPartPlain inPhase outPhase
  split := splitScc
  finish decls := do
    let irDecls ← IR.toIR decls
    discard <| IR.compile irDecls
  implementedBy := fun _ _ => pure ()
  postponed := fun _ => pure ()

partial def runWithRunner (declNames : Array Name) (baseOpts : Options)
    (simplifiedProfile : Bool) (runner : DriverRunner) : CompilerM Unit := withAtLeastMaxRecDepth 8192 do
  /-
  Note: we need to increase the recursion depth because we currently do to save phase1
  declarations in .olean files. Then, we have to recursively compile all dependencies,
  and it often creates a very deep recursion.
  Moreover, some declarations get very big during simplification.
  -/

  if (← declNames.anyM isInductive) then
    -- Eagerly compute and persist the cross-module inductive infos for these inductive types in
    -- their defining module. The computation walks each constructor's field types, which can
    -- reference constants from non-transitively (privately) imported modules; the defining module is
    -- the only place where that walk is guaranteed to succeed, so consumers rely on the persisted
    -- result. This could be postponed as well but the added complexity is likely not worth the
    -- slight gain in rebuild avoidance/parallelism.
    compileInductives declNames
    return

  for declName in declNames do
    if let some fnName := Compiler.getImplementedBy? (← getEnv) declName then
      if (← getEnv).header.isModule && (← compiler.postponeCompile.getM) then
        -- must postpone here as well so that visibility marking happens in the correct process
        modifyEnv (postponedCompileDeclsExt.addEntry · { declNames := #[declName], options := ← getOptions })
      else
        -- Ensure the impl target is compiled first so `getLocalDeclAt?` succeeds
        resumeCompilation fnName baseOpts
        if !isDeclPublic (← getEnv) fnName then
          if let some decl ← getLocalDeclAt? fnName .base then
            runner.implementedBy fnName declName
            LCNF.markDeclPublicRec .base decl
            if let some decl ← getLocalDeclAt? fnName .mono then
              LCNF.markDeclPublicRec .mono decl
              if let some decl ← getLocalDeclAt? fnName .impure then
                LCNF.markDeclPublicRec .impure decl
  let declNames ← declNames.filterM (shouldGenerateCode ·)
  if declNames.isEmpty then return
  for declName in declNames do
    if declName == `main then
      if let some info ← getDeclInfo? declName then
        if !(isValidMainType info.type) then
          throwError "`main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`"

  let decls ← declNames.mapM toDecl
  for decl in decls do
    checkMeta decl

  -- Now that we have done all input checks, check for postponement
  if (← getEnv).header.isModule && (← compiler.postponeCompile.getM) then
    modifyEnv (postponedCompileDeclsExt.addEntry · { declNames := decls.map (·.name), options := ← getOptions })
    -- meta defs are compiled locally so they are available for execution/compilation without
    -- importing `.ir` but still marked for `leanir` compilation so that we do not have to persist
    -- module-local compilation information between the two processes
    if decls.any (isMarkedMeta (← getEnv) ·.name) then
      -- avoid re-compiling the meta defs in this process; the entry for `leanir` is not affected
      modifyEnv (postponedCompileDeclsExt.modifyState · fun s => decls.foldl (·.erase ·.name) s)
    else
      runner.postponed (decls.map (·.name))
      return

  -- Compile any postponed dependencies first.
  -- In leanir, we visit declarations in the original order, but this can still be necessary for
  -- compiling non-meta defs on demand at `#eval` etc.
  for decl in decls do
    decl.value.forCodeM fun code => code.forM fun c => do
      let .let { value := .const c .., .. } .. := c | return
      -- Need to do some lookups to get the actual name passed to `compileDecls`
      let c := Compiler.getImplementedBy? (← getEnv) c |>.getD c
      resumeCompilation c baseOpts

  let decls := markRecDecls decls
  let manager ← getPassManager
  let manager := if simplifiedProfile then manager.simplified else manager
  let isCheckEnabled := compiler.check.get (← getOptions)
  let decls ← runner.runPart .pure .pure "compilation (LCNF base)" manager.basePasses decls isCheckEnabled
  let decls ← runner.runPart .pure .pure "compilation (LCNF mono)" manager.monoPasses decls isCheckEnabled
  let sccs ← runner.split decls
  for decls in sccs do
    let decls ← runner.runPart .pure .impure "compilation (LCNF mono)" manager.monoPassesNoLambda decls isCheckEnabled
    withPhase .impure do
      let decls ← runner.runPart .impure .impure "compilation (LCNF impure)" manager.impurePasses decls isCheckEnabled

      runner.finish decls

/-- Reference-compatible diagnostic driver with optional conservative pass selection. -/
def runWithProfile (declNames : Array Name) (baseOpts : Options)
    (simplifiedProfile : Bool) : CompilerM Unit :=
  runWithRunner declNames baseOpts simplifiedProfile diagnosticRunner

/-- Compatibility entry for the former nested diagnostic phase runner. -/
def runWithProfile.runPassManagerPart (inPhase outPhase : Purity) (profilerName : String)
    (passes : Array Pass) (decls : Array (Decl inPhase)) (isCheckEnabled : Bool) :
    CompilerM (Array (Decl outPhase)) :=
  runPassManagerPartDiagnostic inPhase outPhase profilerName passes decls isCheckEnabled

/-- Reference driver, retaining the original public signature and pass list. -/
def run (declNames : Array Name) (baseOpts : Options) : CompilerM Unit :=
  runWithProfile declNames baseOpts false

/-- Compatibility entry for users inspecting the original per-phase runner. -/
def run.runPassManagerPart (inPhase outPhase : Purity) (profilerName : String)
    (passes : Array Pass) (decls : Array (Decl inPhase)) (isCheckEnabled : Bool) :
    CompilerM (Array (Decl outPhase)) :=
  runWithProfile.runPassManagerPart inPhase outPhase profilerName passes decls isCheckEnabled

end PassManager

def main (declNames : Array Name) (baseOpts : Options) : CoreM Unit := do
  withTraceNode `Compiler (fun _ => return m!"compiling: {declNames}") do
    CompilerM.run <| PassManager.run declNames baseOpts

/-- Conservative profile using the plain runner, even when diagnostic flags
are enabled by the caller. The policy is carried through dependency resumption. -/
def mainSimplified (declNames : Array Name) (baseOpts : Options) : CoreM Unit :=
  withOptions (simplifiedRunnerOptions false) do
    CompilerM.run <| PassManager.runWithRunner declNames
      (simplifiedRunnerOptions false baseOpts) true PassManager.plainRunner

/-- The same conservative pass selection with the diagnostic runner available
for development. No pass algorithm or checking policy changes between modes. -/
def mainSimplifiedDiagnostic (declNames : Array Name) (baseOpts : Options) : CoreM Unit :=
  withOptions (simplifiedRunnerOptions true) do
    withTraceNode `Compiler (fun _ => return m!"compiling (simplified): {declNames}") do
      CompilerM.run <| PassManager.runWithProfile declNames (simplifiedRunnerOptions true baseOpts) true

/-- Automatic compilation selects a profile; the default remains reference. -/
def compileWithProfile (declNames : Array Name) (baseOpts : Options) : CoreM Unit := do
  if compiler.simplified.get (← getOptions) then
    if compiler.simplified.diagnostics.get (← getOptions) then
      mainSimplifiedDiagnostic declNames baseOpts
    else
      mainSimplified declNames baseOpts
  else
    main declNames baseOpts

builtin_initialize
  compileDeclsRef.set compileWithProfile

builtin_initialize
  registerTraceClass `Compiler.init (inherited := true)
  registerTraceClass `Compiler.test (inherited := true)
  registerTraceClass `Compiler.result (inherited := true)
  registerTraceClass `Compiler.jp

end Lean.Compiler.LCNF
