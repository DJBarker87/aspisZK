import AspisV8R19.OracleProgramOps

/-! Finite causal programs over arbitrary addresses have a finite potential
query support when answers are finite. This removes the need to posit a
uniform distribution on the infinite type of all byte-list oracle tables.
Support includes ALL answer branches, not just the realized transcript. -/
set_option autoImplicit false
namespace AspisV8R19.OracleFiniteSupport
open MemoizedProgramLaw OracleResampling OracleProgramOps
variable {I A O : Type} [Fintype A] [DecidableEq I]
noncomputable section

def support : Program I A O → Finset I
  | .done _ => ∅
  | .ask i next => {i} ∪ Finset.univ.biUnion (fun a => support (next a))

theorem head_mem (i : I) (next : A → Program I A O) : i ∈ support (.ask i next) := by
  simp [support]

theorem child_subset (i : I) (next : A → Program I A O) (a : A) :
    support (next a) ⊆ support (.ask i next) := by
  intro j hj
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,hj⟩)

def restrict (p : Program I A O) (s : Finset I) (h : support p ⊆ s) :
    Program {i // i ∈ s} A O :=
  match p with
  | .done o => .done o
  | .ask i next => .ask ⟨i,h (head_mem i next)⟩
      (fun a => restrict (next a) s ((child_subset i next a).trans h))

theorem rename_restrict (p : Program I A O) (s : Finset I) (h : support p ⊆ s) :
    rename Subtype.val (restrict p s h) = p := by
  induction p with
  | done o => rfl
  | ask i next ih =>
      simp only [restrict,rename]
      congr 1
      funext a
      exact ih a ((child_subset i next a).trans h)

def extend (s : Finset I) (H : {i // i ∈ s} → A) (fallback : A) (i : I) : A :=
  if h : i ∈ s then H ⟨i,h⟩ else fallback

theorem extend_at (s : Finset I) (H : {i // i ∈ s} → A) (fallback : A)
    (i : {i // i ∈ s}) : extend s H fallback i.val = H i := by
  simp [extend,i.property]

theorem eval_restrict (p : Program I A O) (s : Finset I) (h : support p ⊆ s)
    (H : {i // i ∈ s} → A) (fallback : A) :
    eval (extend s H fallback) p = mapView Subtype.val (eval H (restrict p s h)) := by
  conv_lhs => rw [← rename_restrict p s h]
  rw [eval_rename]
  have heq : extend s H fallback ∘ Subtype.val = H := by
    funext i; exact extend_at s H fallback i
  rw [heq]

theorem finite_support_oracle_law [Nonempty A] (p : Program I A O)
    (s : Finset I) (h : support p ⊆ s) (fallback : A) (observe : View I A O → ℚ) :
    mean (fun H : {i // i ∈ s} → A => observe (eval (extend s H fallback) p)) =
      lazyMean p (fun _ => none) observe := by
  calc
    _ = mean (fun H : {i // i ∈ s} → A =>
        observe (mapView Subtype.val (eval H (restrict p s h)))) := by
          apply mean_congr; intro H; rw [eval_restrict]
    _ = lazyMean (restrict p s h) (fun _ => none) (fun r => observe (mapView Subtype.val r)) :=
      empty_oracle_law (restrict p s h) (fun r => observe (mapView Subtype.val r))
    _ = lazyMean (rename Subtype.val (restrict p s h)) (fun _ => none) observe :=
      (lazy_rename Subtype.val Subtype.val_injective (restrict p s h) (fun _ => none) observe).symm
    _ = _ := by rw [rename_restrict]

theorem finite_support_law_independent_of_fallback [Nonempty A] (p : Program I A O)
    (s : Finset I) (h : support p ⊆ s) (a b : A) (observe : View I A O → ℚ) :
    mean (fun H : {i // i ∈ s} → A => observe (eval (extend s H a) p)) =
      mean (fun H : {i // i ∈ s} → A => observe (eval (extend s H b) p)) := by
  rw [finite_support_oracle_law p s h a, finite_support_oracle_law p s h b]

#print axioms head_mem
#print axioms child_subset
#print axioms rename_restrict
#print axioms extend_at
#print axioms eval_restrict
#print axioms finite_support_oracle_law
#print axioms finite_support_law_independent_of_fallback
end
end AspisV8R19.OracleFiniteSupport
