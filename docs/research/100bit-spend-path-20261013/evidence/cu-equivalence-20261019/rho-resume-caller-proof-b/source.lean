import AspisR1RhoResumeCaller.Funs
import CuSavingsRhoReader
import CuSavingsRhoResumeCanonical
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoResumeCaller
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
open CuSavingsRhoInitRow CuSavingsRhoResumeLoans

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

private def sourceTry {A B : Type} (m : Result (core.result.Result A verifier.Error))
    (f : A → Result (core.result.Result B verifier.Error)) :
    Result (core.result.Result B verifier.Error) := do
  let r ← m
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue v => f v
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      B (core.convert.FromSame verifier.Error) residual

private theorem try_success {A B : Type} (m : Result (core.result.Result A verifier.Error))
    (f : A → Result (core.result.Result B verifier.Error)) (out : B)
    (h : sourceTry m f = .ok (.Ok out)) :
    ∃ value,m = .ok (.Ok value) ∧ f value = .ok (.Ok out) := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok r =>
    cases r with
    | Err e => cases h
    | Ok v => exact ⟨v,rfl,h⟩

theorem read_success (reader after : ResumeReader) (q : aspis_core.field.QM31)
    (h : source_read_k reader = .ok (.Ok (q,after))) : Canonical q := by
  unfold source_read_k at h
  obtain ⟨pair,hs,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨r,after'⟩
  cases r with
  | Err e => cases h
  | Ok value =>
    cases core.result.Result.Ok.inj (Result.ok.inj h)
    exact (CuSavingsRhoReader.k_success reader after q hs).1

theorem weights_success (weights restored : alloc.vec.Vec aspis_core.field.QM31)
    (reader after : ResumeReader)
    (h : source_resume_weights weights reader = .ok (.Ok (restored,after))) :
    CanonicalFrom restored 0 ∧ restored.val.length=weights.val.length := by
  unfold source_resume_weights at h
  obtain ⟨r,hs,h⟩ := bind_ok _ _ _ h
  cases r with
  | Err e => cases h
  | Ok pair =>
    cases core.result.Result.Ok.inj (Result.ok.inj h)
    have hc := CuSavingsRhoResumeCanonical.source_success weights restored reader after hs
    exact ⟨hc.2.1,hc.1⟩

variable [ResumeCommon]
theorem allocation_length (v : transport.Variant) (weights : alloc.vec.Vec aspis_core.field.QM31)
    (h : source_resume_allocate v = .ok (.Ok weights)) : weights.val.length ≤ 256 := by
  letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve ResumeCommon.allocationBackend
  unfold source_resume_allocate at h
  rw [CuSavingsRhoAccumulatorNew.final_len_success] at h
  simp only [bind_tc_ok] at h
  obtain ⟨r,hs,h⟩ := bind_ok _ _ _ h
  cases r with
  | Err e => cases h
  | Ok raw =>
    cases core.result.Result.Ok.inj (Result.ok.inj h)
    have hlen := CuSavingsRhoHeap.source_length sourceCopy
      (CuSavingsRhoAccumulatorNew.length v) sourceZero weights hs
    rw [hlen]
    exact CuSavingsRhoAccumulatorNew.length_bound v

/-- Successful whole unchanged resume derives every canonicality/length
premise needed by the source stage. Common fragments are arbitrary computations
and cannot access or overwrite the retained decoded rho and power. -/
theorem source_inputs {H : Type} (digest : aspis_core.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (h : source_resume_caller digest bytes proof public1 v hash = .ok (.Ok (p,a))) :
    Canonical p.rho ∧ Canonical a.power ∧ CanonicalFrom a.weights 0 ∧
      (alloc.vec.Vec.len a.weights).val ≤ 256 := by
  unfold source_resume_caller at h
  obtain ⟨r0,_,h⟩ := bind_ok _ _ _ h
  cases r0 with
  | Err e => cases h
  | Ok begin =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨r1,hr,h⟩ := bind_ok _ _ _ h
    cases r1 with
    | Err e => cases h
    | Ok rhoPair =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      rcases rhoPair with ⟨rho,r⟩
      dsimp only at h
      have hrho := read_success begin.r r rho hr
      obtain ⟨r2,_,h⟩ := bind_ok _ _ _ h
      cases r2 with
      | Err e => cases h
      | Ok middle =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        obtain ⟨r3,hp,h⟩ := bind_ok _ _ _ h
        cases r3 with
        | Err e => cases h
        | Ok powerPair =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          rcases powerPair with ⟨power,r'⟩
          dsimp only at h
          have hpower := read_success middle.r r' power hp
          obtain ⟨r4,ha,h⟩ := bind_ok _ _ _ h
          cases r4 with
          | Err e => cases h
          | Ok weights =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            have hl := allocation_length v weights ha
            obtain ⟨r5,hw,h⟩ := bind_ok _ _ _ h
            cases r5 with
            | Err e => cases h
            | Ok weightPair =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
              rcases weightPair with ⟨restored,after⟩
              dsimp only at h
              obtain ⟨hcanonical,hlen⟩ := weights_success weights restored r' after hw
              split at h
              · cases h
              · obtain ⟨i,_,h⟩ := bind_ok _ _ _ h
                simp only [lift,bind_tc_ok] at h
                cases core.result.Result.Ok.inj (Result.ok.inj h)
                refine ⟨hrho,hpower,hcanonical,?_⟩
                simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length,hlen] using hl

#print axioms read_success
#print axioms weights_success
#print axioms allocation_length
#print axioms source_inputs
end AspisR1.CuSavingsRhoResumeCaller
