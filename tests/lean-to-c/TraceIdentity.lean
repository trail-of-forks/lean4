module
import Lean

/-! Record the stock compiler pass trace for the scalar identity declaration. -/

set_option compiler.postponeCompile false
set_option trace.Compiler true

@[noinline, export lean_to_c_trace_identity]
def traceIdentity (x : UInt32) : UInt32 := x

set_option trace.Compiler false
set_option pp.all true in
#print traceIdentity

example (x : UInt32) : traceIdentity x = x := rfl
