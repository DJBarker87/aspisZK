import NLU_ConstructComplete
import NMC_ParentState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Frame
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Q := NLC_Finish.Q
/-- Mirrors the initialized projections of NMC_segments::Parent. Fields
whose source lifetime has not begun are ghost slots, never native reads. -/
structure Value where
 running : Q
 alpha : NLC_Finish.Alpha
 transcript : r1_wire.SemanticTranscript Unit
 challenges : r1_wire.Challenges
 claims : NMC_Parent.OwnedClaims
 terminal : Q
 mask : Q
 extra : NLC_Finish.Words
 before : NLC_Finish.Words
 state : Array U8 32#usize
 z0 : NLC_Finish.Point
 z1 : NLC_Finish.Point
 rest : Array U8 32#usize
 reservation : Nat
/-- Constructor-free selector from the native harness; all array/word domains
are observation indices, not restrictions on the caller's field values. -/
def field (v : Value) (tag : Fin 23) (i : Fin 87) (j : Fin 4) : Nat :=
 let qword:=fun q=>(NLU.word q j).val
 let cell:=fun (a : NLC_Finish.Words)=>NLU.cell a (i.val%29) (Nat.mod_lt _ (by decide))
 match tag.val with
 | 0=>qword v.running
 | 1=>qword (NLU.cell v.alpha (i.val%10) (Nat.mod_lt _ (by decide)))
 | 2=>qword (NLU.cell (NLU.cell v.claims.value (i.val/29) (by change i.val/29<3;omega)) (i.val%29) (Nat.mod_lt _ (by decide)))
 | 3=>qword v.terminal
 | 4=>qword v.mask
 | 5=>qword (cell v.extra)
 | 6=>qword (cell v.before)
 | 7=>(NLU.cell v.state (i.val%32) (Nat.mod_lt _ (by decide))).val
 | 8=>qword v.z0.x
 | 9=>qword v.z0.y
 | 10=>qword v.z1.x
 | 11=>qword v.z1.y
 | 12=>(NLU.cell v.rest (i.val%32) (Nat.mod_lt _ (by decide))).val
 | 13=>v.reservation
 | 14=>v.claims.identity
 | 15=>(NLU.cell v.transcript.state (i.val%32) (Nat.mod_lt _ (by decide))).val
 | 16=>v.transcript.next_row.val
 | 17=>qword v.challenges.lambda
 | 18=>qword v.challenges.chi
 | 19=>qword v.challenges.theta
 | 20=>qword (NLU.cell v.challenges.zc (i.val%10) (Nat.mod_lt _ (by decide)))
 | 21=>qword v.challenges.mu
 | _=>qword v.challenges.eta
end AspisR1.NMC_Frame
end
