import R1Z.PV_Src_PortInternalRounds

/-! Successful finite round runs retain canonical arithmetic state even when
trace callbacks are arbitrary Result-valued computations. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortTraceCanonical
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_Src_PortTraceRounds

theorem full {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (kind : Usize → poseidon2.Poseidon2RoundKind) (xs : List (Usize × State))
    (s input : State) (trace : F) (round : U8) (hs : Canonical s)
    (out : Output F) (hr : fullSteps callback kind xs s trace round input = ok out) :
    Canonical out.1 := by
  induction xs generalizing s input trace round with
  | nil =>
    change ok (s,trace,round,input) = ok out at hr
    have he := Result.ok.inj hr
    rw [← he]
    exact hs
  | cons p xs ih =>
    rcases p with ⟨index,c⟩
    rw [fullSteps] at hr
    obtain ⟨state1,hstate,rest⟩ := bind_ok_inv hr
    obtain ⟨callback1,hcallback,hresult⟩ := bind_ok_inv rest
    obtain ⟨expected,hexpected,hcan⟩ := full_total s c
    have he : state1=expected := Result.ok.inj (hstate.symm.trans hexpected)
    have hstatecan : Canonical state1 := by rw [he];exact hcan
    exact ih state1 state1 callback1.2 (U8.wrapping_add round 1#u8) hstatecan hresult

theorem internal {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (xs : List (Usize × U32)) (s input : State) (trace : F) (round : U8)
    (hs : Canonical s) (out : Output F)
    (hr : PV_Src_PortInternalRounds.steps callback xs s trace round input = ok out) :
    Canonical out.1 := by
  induction xs generalizing s input trace round with
  | nil =>
    change ok (s,trace,round,input) = ok out at hr
    have he := Result.ok.inj hr
    rw [← he]
    exact hs
  | cons p xs ih =>
    rcases p with ⟨index,c⟩
    rw [PV_Src_PortInternalRounds.steps] at hr
    obtain ⟨state1,hstate,rest⟩ := bind_ok_inv hr
    obtain ⟨callback1,hcallback,hresult⟩ := bind_ok_inv rest
    obtain ⟨expected,hexpected,hcan⟩ := PV_Src_PortInternalRounds.total s c
    have he : state1=expected := Result.ok.inj (hstate.symm.trans hexpected)
    have hstatecan : Canonical state1 := by rw [he];exact hcan
    exact ih state1 state1 callback1.2 (U8.wrapping_add round 1#u8) hstatecan hresult

#print axioms full
#print axioms internal
end R1Z.PV_Src_PortTraceCanonical
