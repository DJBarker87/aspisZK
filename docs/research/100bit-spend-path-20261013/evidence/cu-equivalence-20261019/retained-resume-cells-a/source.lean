import CuSavingsRhoResumeCaller
import CuSavingsRetainedResumeOrigins
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedResumeCells
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
/-! Narrow source interpretation of the fixed mutable-array fill. It executes
exactly n checked Reader.k calls, left-to-right, threading the same owned
reader. Each successful call writes exactly one previously unobservable cell;
on any Rust error, runtime failure or divergence it exits immediately.
The correspondence to the source's ten-cell MutArray iteration/handback is
an explicit standard owning-array boundary, not a new canonicality premise. -/
def cells : (n : Nat) → ResumeReader →
    Result (core.result.Result ({xs : List aspis_core.field.QM31 // xs.length=n} × ResumeReader) verifier.Error)
  | 0,r => .ok (.Ok (⟨[],rfl⟩,r))
  | n+1,r => do
    let value ← source_read_k r
    match value with
    | .Err error => .ok (.Err error)
    | .Ok (q,r1) =>
      let rest ← cells n r1
      match rest with
      | .Err error => .ok (.Err error)
      | .Ok (qs,r2) => .ok (.Ok (⟨q::qs.val,by simp only [List.length_cons,qs.property]⟩,r2))

private theorem bind_ok {A B : Type} (m : Result A) (f : A→Result B) (out : B)
    (h : (m >>= f)=.ok out) : ∃ x,m=.ok x ∧ f x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem source_success (n : Nat) (r after : ResumeReader)
    (qs : {xs : List aspis_core.field.QM31 // xs.length=n})
    (h : cells n r=.ok (.Ok (qs,after))) :
    ∀ q,q∈qs.val → CuSavingsRhoInitRow.Canonical q := by
  induction n generalizing r after with
  | zero =>
    simp only [cells,Result.ok.injEq,core.result.Result.Ok.injEq,Prod.mk.injEq] at h
    cases h.1
    simp
  | succ n ih =>
    unfold cells at h
    obtain ⟨value,hs,h⟩ := bind_ok _ _ _ h
    cases value with
    | Err error => cases h
    | Ok pair =>
      rcases pair with ⟨q,r1⟩
      simp only [uncurry_apply_pair] at h
      obtain ⟨rest,hr,h⟩ := bind_ok _ _ _ h
      cases rest with
      | Err error => cases h
      | Ok pair =>
        rcases pair with ⟨tail,r2⟩
        simp only [uncurry_apply_pair] at h
        have ht := ih r1 r2 tail hr
        have hh := CuSavingsRhoResumeCaller.read_success r r1 q hs
        cases core.result.Result.Ok.inj (Result.ok.inj h)
        intro x hx
        rcases List.mem_cons.mp hx with he|he
        · simpa only [he] using hh
        · exact ht x he

#print axioms source_success
end AspisR1.CuSavingsRetainedResumeCells
