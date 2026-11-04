module
import Lean
import Lean.Compiler.LCNF.ScalarC
public meta import Lean
public meta import Lean.Compiler.LCNF.ScalarC

/-! Generate both C outputs and a Lean AST from a Lean-source identity function. -/

set_option compiler.postponeCompile false

@[noinline, export lean_to_c_identity]
def backendIdentity (x : UInt32) : UInt32 := x

@[noinline] def unsupportedIdentity (x : UInt64) : UInt64 := x

open Lean Compiler LCNF in
run_meta do
  let some directory ← IO.getEnv "LEAN_TO_C_DEMO_OUT"
    | throwError "set LEAN_TO_C_DEMO_OUT to the output directory"
  let directory : System.FilePath := directory
  IO.FS.createDirAll directory
  let modName ← getMainModule
  let roots := #[``backendIdentity]
  let original ← emitCForDeclsOriginal modName roots
  let current ← emitCForDecls modName roots
  let structured ← ScalarC.emitCForDecls modName roots
  unless original.toUTF8 == structured.toUTF8 && current.toUTF8 == structured.toUTF8 do
    throwError "scalar C backend differs from the original C output"
  let rejected ← try
    let _ ← ScalarC.emitCForDecls modName #[``unsupportedIdentity]
    pure false
  catch _ => pure true
  unless rejected do throwError "scalar C backend accepted an unsupported UInt64 declaration"
  let function ← ScalarC.lowerDecl modName ``backendIdentity
  IO.FS.writeFile (directory / "original.c") original
  IO.FS.writeFile (directory / "structured.c") structured
  IO.FS.writeFile (directory / "function.c")
    ("#include <stdint.h>\n#define LEAN_EXPORT\n" ++ ScalarC.render function)
  IO.FS.writeFile (directory / "ScalarIdentity.lean")
    ("/- Generated from Lean 4.35 impure LCNF. Do not edit. -/\n" ++
     "import Backend.ScalarCAST\n\nnamespace Examples.Generated.ScalarIdentity\n\n" ++
     "def function : Lean.Compiler.LCNF.ScalarC.Function :=\n" ++
     "  { name := " ++ reprStr function.name ++ ", parameter := " ++ reprStr function.parameter ++ " }\n\n" ++
     "end Examples.Generated.ScalarIdentity\n")
  IO.FS.writeFile (directory / "names.json") (Json.compress (Json.mkObj
    [("function", toJson function.name), ("parameter", toJson function.parameter)]))
