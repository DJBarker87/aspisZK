import NJR_Cuts
set_option autoImplicit false
noncomputable section
namespace NJR_FlushComposition
open Aeneas Aeneas.Std Result AspisR1
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev Row := Port3_NativePendingBody.Row

/-- Complete arbitrary-index store windows compose by finite induction. The
reply at each site is the CLOSED value model on that SAME raw cell. Neither
whole-buffer native execution nor a successful flush premise is required. -/
theorem windows (b : VTop_Stages.verifier.BatchedWeights)
 (rawSize : b.raw.val.length=64) (states : Nat → List K)
 (sizes : ∀ n, n≤64 → (states n).length=64)
 (steps : ∀ i, i<64 → ∀ j, j<64 →
  (states (i+1))[j]? = if i=j then (b.raw.val[i]?).map NJJ_Flush.cell else (states i)[j]?) :
 states 64=(NJJ_Flush.output b).val := by
 have invariant : ∀ n, n≤64 → ∀ j, j<n →
  (states n)[j]?=(b.raw.val[j]?).map NJJ_Flush.cell := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro hn j hj
    rw [steps n (by omega) j (by omega)]
    by_cases same : n=j
    · subst j; rw [if_pos rfl]
    · rw [if_neg same];exact ih (by omega) j (by omega)
 apply List.ext_getElem?
 intro j
 change (states 64)[j]?=(b.raw.val.map NJJ_Flush.cell)[j]?
 by_cases inside : j<64
 · rw [List.getElem?_map]
   exact invariant 64 (by omega) j inside
 · rw [List.getElem?_eq_none (by rw [sizes 64 (by omega)];omega),
   List.getElem?_eq_none (by simp only [List.length_map,rawSize];omega)]

/-- Forward instantiation of the already CLOSED value/source law and the
reviewed native stores, with all cells identified by the finite induction. -/
theorem source (b : VTop_Stages.verifier.BatchedWeights) (old : Slice K)
 (rawSize : b.raw.val.length=64) (oldSize : old.val.length=64)
 (states : Nat → List K) (sizes : ∀ n,n≤64→(states n).length=64)
 (steps : ∀ i,i<64→∀ j,j<64→(states (i+1))[j]?=
  if i=j then (b.raw.val[i]?).map NJJ_Flush.cell else (states i)[j]?) :
 Port3_FlushInstall.flush b old=ok (NJJ_Flush.output b) ∧
 states 64=(NJJ_Flush.output b).val ∧
 (∀ q∈states 64,Port3_FlushInstall.Canonical q) := by
 have values:=windows b rawSize states sizes steps
 refine ⟨NJJ_Flush.source b old rawSize oldSize,values,?_⟩
 rw [values]
 exact NJJ_Flush.canonical b

#print axioms windows
#print axioms source
end NJR_FlushComposition
