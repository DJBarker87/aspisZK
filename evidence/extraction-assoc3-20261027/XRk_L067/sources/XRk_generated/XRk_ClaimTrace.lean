import XRk_PowersAssociation
import XRk_CollectLaws
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRk_ClaimTrace
abbrev E := aspis_core.field.wide_exact.WideExact
def parts {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize) : Result (Option (List E)) :=
  (List.range 6).foldlM (XRk_CollectLaws.step (XRk_preparedPart sem y1 g)) (some [])
def weighted (powers parts : List E) (inactive zero : E) : Result E :=
  (powers.zip (inactive::parts)).foldlM (fun sum (k,p) => do
    let term ← aspis_core.field.wide_exact.WideExact.mul k p
    aspis_core.field.wide_exact.WideExact.add sum term) zero

theorem powers_length (x : E) (n : Nat) (p : E) (out : List E)
    (run : XRk_powers x n p = ok out) : out.length=n := by
  induction n generalizing p out with
  | zero => cases run; rfl
  | succ n ih =>
    cases n with
    | zero => cases run; rfl
    | succ k =>
      simp only [XRk_powers] at run
      obtain ⟨q,_,run⟩ := bind_success _ _ _ run
      obtain ⟨rest,hrest,run⟩ := bind_success _ _ _ run
      have same : p::rest=out := Result.ok.inj run
      subst out
      simp only [List.length_cons,ih q rest hrest]

theorem trace {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (inactive : E)
    (g : Array E 29#usize) (kappa claim : E)
    (run : verifier.prepared_claim D sem y1 inactive g kappa = ok (.Ok claim)) :
    ∃ one zero powers partValues,
      aspis_core.field.wide_exact.WideExact.ONE=ok one ∧
      aspis_core.field.wide_exact.WideExact.ZERO=ok zero ∧
      XRk_powers kappa 7 one=ok powers ∧ powers.length=7 ∧
      parts sem y1 g=ok (some partValues) ∧ partValues.length=6 ∧
      weighted powers partValues inactive zero=ok claim := by
  unfold verifier.prepared_claim at run
  obtain ⟨one,hone,run⟩ := bind_success _ _ _ run
  obtain ⟨zero,hzero,run⟩ := bind_success _ _ _ run
  obtain ⟨powers,hpowers,run⟩ := bind_success _ _ _ run
  obtain ⟨result,hparts,run⟩ := bind_success _ _ _ run
  cases result with
  | none => cases run
  | some partValues =>
    obtain ⟨value,hweighted,run⟩ := bind_success _ _ _ run
    have same : value=claim := core.result.Result.Ok.inj (Result.ok.inj run)
    have hparts' : parts sem y1 g=ok (some partValues) := by
      unfold parts
      have hs : XRk_CollectLaws.step (XRk_preparedPart sem y1 g) =
          (fun (seed : Option (List E)) point => match seed with
           | none => ok none
           | some xs => do
             let p ← XRk_preparedPart sem y1 g point
             ok (p.map (fun p => xs++[p]))) := by
        funext seed point
        cases seed <;> rfl
      rw [hs]
      exact hparts
    have plen := XRk_CollectLaws.length_of_success
      (XRk_preparedPart sem y1 g) (List.range 6) [] partValues hparts'
    refine ⟨one,zero,powers,partValues,hone,hzero,hpowers,powers_length _ _ _ _ hpowers,hparts',?_,?_⟩
    · simpa only [List.length_nil,List.length_range,Nat.zero_add] using plen
    · exact hweighted.trans (congrArg Result.ok same)
#print axioms powers_length
#print axioms trace
end XRk_ClaimTrace
