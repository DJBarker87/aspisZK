module
import all R0P.Poseidon
import NJA_Trace

public section
set_option autoImplicit false
namespace NJA_TraceModel

def kind : NJA_Trace.Kind → R0P.PoseidonRoundKind
 | .initial i => .externalInitial i
 | .internal i => .internal i
 | .final i => .externalFinal i

theorem descriptor (n : Nat) (hn : n<22) :
 R0P.poseidonRoundKind n = some (kind (NJA_Trace.kind n)) := by
 unfold R0P.poseidonRoundKind NJA_Trace.kind
 by_cases a : n<4
 · simp [a,kind]
 · by_cases b : n<18
   · simp [a,b,kind]
   · simp [a,b,hn,kind]

#check R0P.poseidon_rounds_split
#print axioms descriptor
end NJA_TraceModel
