import R1Z.PV_Src_PortPermutation
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ConstantCallback16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_Src_PortTraceRounds
variable {F : Type}
def replace (trace : F) (out : Output Unit) : Output F :=
  (out.1,trace,out.2.2.1,out.2.2.2)

theorem full (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (trace : F) (hc : ∀ event, callback.call_mut trace event = ok ((),trace))
    (kind : Usize → poseidon2.Poseidon2RoundKind) (xs : List (Usize × State))
    (s input : State) (round : U8) (out : Output Unit)
    (ho : fullSteps PV_Src_PortNoop.callback kind xs s () round input = ok out) :
    fullSteps callback kind xs s trace round input = ok (replace trace out) := by
  induction xs generalizing s input round out with
  | nil =>
    have h := Result.ok.inj ho
    rw [← h]
    rfl
  | cons p xs ih =>
    rw [fullSteps] at ho
    obtain ⟨next,hn,rest⟩ := R0Z.PoseidonRefine.bind_ok_inv ho
    simp only [PV_Src_PortNoop.call,bind_tc_ok] at rest
    rw [fullSteps,hn]
    simp only [bind_tc_ok,hc]
    exact ih next next (U8.wrapping_add round 1#u8) out rest

theorem internal (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (trace : F) (hc : ∀ event, callback.call_mut trace event = ok ((),trace))
    (xs : List (Usize × U32)) (s input : State) (round : U8) (out : Output Unit)
    (ho : PV_Src_PortInternalRounds.steps PV_Src_PortNoop.callback xs s () round input = ok out) :
    PV_Src_PortInternalRounds.steps callback xs s trace round input = ok (replace trace out) := by
  induction xs generalizing s input round out with
  | nil =>
    have h := Result.ok.inj ho
    rw [← h]
    rfl
  | cons p xs ih =>
    rw [PV_Src_PortInternalRounds.steps] at ho
    obtain ⟨next,hn,rest⟩ := R0Z.PoseidonRefine.bind_ok_inv ho
    simp only [PV_Src_PortNoop.call,bind_tc_ok] at rest
    rw [PV_Src_PortInternalRounds.steps,hn]
    simp only [bind_tc_ok,hc]
    exact ih next next (U8.wrapping_add round 1#u8) out rest
#print axioms full
#print axioms internal
end R1Z.PV_RunJoin_ConstantCallback16
