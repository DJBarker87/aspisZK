import R1Z.PV_B2_F_ConstructorCarrier
set_option autoImplicit false
namespace PV_B2_F_ConstructorEffect
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier
abbrev RustResult := core.result.Result W ProverRwFull.verifier.Error
/-- Box::new is retained at the actual prover caller. An allocation abort is an
outer failure, not a fabricated Rust Error::Allocation return. -/
def finish (boxRequest : Result Unit)
    (r : core.result.Result Weight PV_B2_C_Carrier.verifier.Error) : Result RustResult :=
  match r with
  | .Err e => ok (.Err (toError e))
  | .Ok w => do
    let _ ← boxRequest
    ok (.Ok (toWeight w))

def copied (boxRequest : Result Unit) (v : NV) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) : Result RustResult := do
  let r ← PV_B2_C_WeightsNative.host_weights.Weights.new (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  finish boxRequest r

def original (boxRequest : Result Unit) (v : NV) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) : Result RustResult := do
  let r ← PV_B2_C_ConstructorSuccess.staged (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  finish boxRequest r

/-- All raw inputs and every Box request Result. No input validity, constructor
success or native allocation-success hypothesis is supplied by the caller. -/
theorem complete_result (boxRequest : Result Unit) (v : NV) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) : copied boxRequest v alpha z = original boxRequest v alpha z := by
  unfold copied original
  rw [PV_B2_C_ConstructorSuccess.new_eq_staged]

theorem value_law (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ w : Weight,
      PV_B2_C_WeightsNative.host_weights.Weights.new (fromVariant v)
        (amap fromQ alpha) (amap fromPoint z) = ok (.Ok w) ∧
      copied (ok ()) v alpha z = ok (.Ok (toWeight w)) := by
  obtain ⟨w,hw⟩ := PV_B2_C_ConstructorSuccess.new_total (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  exact ⟨w,hw,by simp only [copied,hw,bind_tc_ok,finish]⟩

theorem failure (e : Error) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    copied (fail e) v alpha z = fail e := by
  obtain ⟨w,hw⟩ := PV_B2_C_ConstructorSuccess.new_total (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  simp only [copied,hw,bind_tc_ok,finish,bind_tc_fail]

theorem divergence (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    copied div v alpha z = div := by
  obtain ⟨w,hw⟩ := PV_B2_C_ConstructorSuccess.new_total (fromVariant v)
    (amap fromQ alpha) (amap fromPoint z)
  simp only [copied,hw,bind_tc_ok,finish,bind_tc_div]

theorem rust_error (boxRequest : Result Unit) (e : PV_B2_C_Carrier.verifier.Error) :
    finish boxRequest (.Err e) = ok (.Err (toError e)) := rfl
#print axioms complete_result
#print axioms value_law
#print axioms failure
#print axioms divergence
#print axioms rust_error
end PV_B2_F_ConstructorEffect
