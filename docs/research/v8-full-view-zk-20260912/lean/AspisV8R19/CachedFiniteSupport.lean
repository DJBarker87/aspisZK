import AspisV8R19.OracleFiniteSupport

/-! Retain an arbitrary existing oracle table on an infinite address type.
Only finite potential future support is randomized. Repeated/cached reads
are never resampled. This does not assert a conditional challenge law. -/
set_option autoImplicit false
namespace AspisV8R19.CachedFiniteSupport
open MemoizedProgramLaw OracleResampling OracleProgramOps OracleFiniteSupport
open AspisV8PairedCommitment
variable {I A O : Type} [Fintype A] [DecidableEq I]
noncomputable section

theorem eval_cached_restrict (p : Program I A O) (s : Finset I) (h : support p ⊆ s)
    (t : Table I A) (H : {i // i ∈ s} → A) (fallback : A) :
    eval (complete t (extend s H fallback)) p =
      mapView Subtype.val (eval (complete (t ∘ Subtype.val) H) (restrict p s h)) := by
  conv_lhs => rw [← rename_restrict p s h]
  rw [eval_rename]
  have heq : complete t (extend s H fallback) ∘ Subtype.val =
      complete (t ∘ Subtype.val) H := by
    funext i
    simp only [Function.comp_apply,complete,extend_at]
  rw [heq]

theorem cached_law [Nonempty A] (p : Program I A O) (s : Finset I) (h : support p ⊆ s)
    (t : Table I A) (fallback : A) (observe : View I A O → ℚ) :
    mean (fun H : {i // i ∈ s} → A =>
      observe (eval (complete t (extend s H fallback)) p)) = lazyMean p t observe := by
  calc
    _ = mean (fun H : {i // i ∈ s} → A => observe
        (mapView Subtype.val (eval (complete (t ∘ Subtype.val) H) (restrict p s h)))) := by
          apply mean_congr; intro H; rw [eval_cached_restrict]
    _ = lazyMean (restrict p s h) (t ∘ Subtype.val)
        (fun r => observe (mapView Subtype.val r)) :=
      exact_oracle_law (I := {i // i ∈ s}) (A := A) (O := O)
        (restrict p s h) (fun i => t i.val) (fun r => observe (mapView Subtype.val r))
    _ = lazyMean (rename Subtype.val (restrict p s h)) t observe :=
      (lazy_rename Subtype.val Subtype.val_injective (restrict p s h) t observe).symm
    _ = _ := by rw [rename_restrict]

theorem own_support_law [Nonempty A] (p : Program I A O)
    (t : Table I A) (fallback : A) (observe : View I A O → ℚ) :
    mean (fun H : {i // i ∈ support p} → A =>
      observe (eval (complete t (extend (support p) H fallback)) p)) = lazyMean p t observe :=
  cached_law p (support p) (fun _ h => h) t fallback observe

#print axioms eval_cached_restrict
#print axioms cached_law
#print axioms own_support_law
end
end AspisV8R19.CachedFiniteSupport
