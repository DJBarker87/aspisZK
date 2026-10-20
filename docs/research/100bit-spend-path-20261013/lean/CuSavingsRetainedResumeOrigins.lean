import CuSavingsRetainedResumeSource
import CuSavingsRetainedCompositionWeightsInputs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedResumeOrigins
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
namespace Q
abbrev E := aspis_core.field.WideExact
abbrev K := aspis_core.field.QM31
end Q
def libra (e : Q.E) : CuSavingsLibraConcrete.L.E :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime]
private theorem bind_ok {A B : Type} (m : Result A) (f : A→Result B) (out : B)
    (h : (m >>= f)=.ok out) : ∃ x,m=.ok x ∧ f x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

def ReaderOrigin (e : Q.E) : Prop :=
  ∃ reader after value,AspisR1CanonicalReader.Reader.e reader=.ok (.Ok value,after) ∧ retained_e value=e

theorem read_origin (r after : ResumeReader) (e : Q.E)
    (h : retained_read_e r=.ok (.Ok e,after)) : ReaderOrigin e := by
  unfold retained_read_e at h
  obtain ⟨pair,hs,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨result,final⟩
  simp only [uncurry_apply_pair] at h
  cases result with
  | Err error => cases h
  | Ok value =>
    have he := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
    exact ⟨retained_to_reader r,final,value,hs,he⟩

theorem reader_alpha (e : Q.E) (h : ReaderOrigin e) : CuSavingsLibraOrigins.Alpha (libra e) := by
  obtain ⟨r,after,value,hs,he⟩ := h
  subst e
  exact CuSavingsLibraOrigins.Alpha.resumed r after value hs

theorem begin_success (header : ResumeHeader) (out : ResumeBegin)
    (h : retained_begin_fields header=.ok (.Ok out)) :
    ReaderOrigin out.gamma ∧ ∃ a0 a1,out.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (libra a0) ∧ CuSavingsLibraOrigins.Alpha (libra a1) := by
  unfold retained_begin_fields at h
  obtain ⟨pair,h0,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨r,r0⟩
  simp only [uncurry_apply_pair] at h
  cases r with
  | Err error => cases h
  | Ok gamma =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨pair,h1,h⟩ := bind_ok _ _ _ h
    rcases pair with ⟨r,r1⟩
    simp only [uncurry_apply_pair] at h
    cases r with
    | Err error => cases h
    | Ok kappa =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨pair,h2,h⟩ := bind_ok _ _ _ h
      rcases pair with ⟨r,r2⟩
      simp only [uncurry_apply_pair] at h
      cases r with
      | Err error => cases h
      | Ok alpha0 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        obtain ⟨pair,h3,h⟩ := bind_ok _ _ _ h
        rcases pair with ⟨r,r3⟩
        simp only [uncurry_apply_pair] at h
        cases r with
        | Err error => cases h
        | Ok alpha1 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          cases core.result.Result.Ok.inj (Result.ok.inj h)
          exact ⟨read_origin header.r r0 gamma h0,alpha0,alpha1,rfl,
            reader_alpha alpha0 (read_origin r1 r2 alpha0 h2),
            reader_alpha alpha1 (read_origin r2 r3 alpha1 h3)⟩

#print axioms read_origin
#print axioms begin_success
end AspisR1.CuSavingsRetainedResumeOrigins
