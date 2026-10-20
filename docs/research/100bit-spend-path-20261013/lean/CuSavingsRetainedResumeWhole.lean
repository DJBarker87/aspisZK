import CuSavingsRetainedResumeBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedResumeWhole
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
open CuSavingsRetainedResumeOrigins CuSavingsRetainedResumeBinding
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime]
private theorem bind_ok {A C : Type} (m : Result A) (f : A→Result C) (out : C)
    (h : (m >>= f)=.ok out) : ∃ x,m=.ok x ∧ f x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem source_inputs (B : Boundaries) {H : Type} (digest : aspis_core.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (h : @source_resume_caller (binding B) H digest bytes proof public1 v hash = .ok (.Ok (p,a))) :
    ReaderOrigin p.gamma ∧
    (∃ a0 a1,p.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (libra a0) ∧ CuSavingsLibraOrigins.Alpha (libra a1)) ∧
    (∀ (i : Nat) (hi : i<p.semantic_alpha.val.length),
      CuSavingsRhoInitRow.Canonical (p.semantic_alpha.val[i]'hi)) := by
  letI : ResumeCommon := binding B
  unfold source_resume_caller at h
  obtain ⟨r0,hbegin,h⟩ := bind_ok _ _ _ h
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
      try simp only [Prod.casesOn] at h
      have hbo := begin_success B digest bytes proof public1 v hash begin hbegin
      obtain ⟨r2,hmiddle,h⟩ := bind_ok _ _ _ h
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
          try simp only [Prod.casesOn] at h
          have hmo := middle_success B r middle hmiddle
          obtain ⟨r4,ha,h⟩ := bind_ok _ _ _ h
          cases r4 with
          | Err e => cases h
          | Ok weights =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h

            obtain ⟨r5,hw,h⟩ := bind_ok _ _ _ h
            cases r5 with
            | Err e => cases h
            | Ok weightPair =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
              rcases weightPair with ⟨restored,after⟩
              try simp only [Prod.casesOn] at h

              change (if (after.«at» != begin.«end») = true then _ else _) = _ at h
              split at h
              · cases h
              · obtain ⟨i,_,h⟩ := bind_ok _ _ _ h
                simp only [lift,bind_tc_ok] at h
                cases core.result.Result.Ok.inj (Result.ok.inj h)
                exact ⟨hbo.1,hbo.2,hmo⟩

#print axioms source_inputs
end AspisR1.CuSavingsRetainedResumeWhole
