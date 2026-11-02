import PV_EVH_NativeRawFinished
import PV_EVH_NonzeroTotal
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyDecision
open Aeneas Aeneas.Std ProverRwFull ControlFlow
open PV_EVH_EntropyHalves (field seed)
variable [ExternalTypes] [ExternalFuns]

def Accepted (mask : Array U8 32#usize) (a : Array U8 64#usize) :
    PV_EVH_NativeEntropyValues.Answer := done (.Ok ⟨mask,field a,seed a⟩)

def Rejected (retry : Usize) : PV_EVH_NativeEntropyValues.Answer :=
  cont (Usize.wrapping_add retry 1#usize)

/-- Every delivered buffer reaches precisely a source success or retry, with
both copies restored. Uses the inherited SYMBOLIC scan termination law; no
normalization of the concrete scan, helper answer premise, or success domain. -/
theorem tests_total (mask : Array U8 32#usize) (retry : Usize)
    (a : Array U8 64#usize) :
    ∃ out, PV_EVH_NativeEntropyValues.tests mask retry a = .ok out ∧
      (out = Rejected retry ∨ out = Accepted mask a) := by
  obtain ⟨b,hb⟩ := PV_EVH_NonzeroTotal.source_total (field a)
  cases b with
  | false =>
    refine ⟨Rejected retry,?_,Or.inl rfl⟩
    simp only [PV_EVH_NativeEntropyValues.tests,hb,bind_tc_ok,
      Bool.false_eq_true,if_false,Rejected,Pure.pure]
  | true =>
    obtain ⟨c,hc⟩ := PV_EVH_NonzeroTotal.source_total (seed a)
    cases c with
    | false =>
      refine ⟨Rejected retry,?_,Or.inl rfl⟩
      simp only [PV_EVH_NativeEntropyValues.tests,hb,hc,bind_tc_ok,
        Bool.false_eq_true,if_false,if_true,Rejected,Pure.pure]
    | true =>
      refine ⟨Accepted mask a,?_,Or.inr rfl⟩
      simp only [PV_EVH_NativeEntropyValues.tests,hb,hc,bind_tc_ok,
        if_true,Accepted,Pure.pure]

theorem rejected_source (mask : Array U8 32#usize) (retry : Usize)
    (a : Array U8 64#usize) (out : PV_EVH_NativeEntropyValues.Answer)
    (h : PV_EVH_NativeEntropyValues.tests mask retry a = .ok out)
    (ha : out ≠ Accepted mask a) : out = Rejected retry := by
  obtain ⟨v,hv,hs⟩ := tests_total mask retry a
  have he : out = v := Result.ok.inj (h.symm.trans hv)
  subst v
  exact hs.resolve_right ha

#print axioms tests_total
#print axioms rejected_source
end PV_EVH_EntropyDecision
