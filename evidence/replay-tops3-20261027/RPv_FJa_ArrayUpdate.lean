import RPv_FIz_SelectorSplit
import RPv_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ArrayUpdate
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
/-- A successful installed write supplies its own index bound. -/
theorem bound {N : Usize} (a b : Array NQ N) (i : Usize) (x : NQ)
    (run : Array.update a i x=ok b) : i.val<N.val := by
  unfold Array.update at run
  split at run
  · cases run
  · rename_i y hy
    have hb := List.getElem?_eq_some_iff.mp hy
    simpa only [a.property] using hb.1
/-- Canonicality of a successful native update, without an assumed bound. -/
theorem canonical_write {N : Usize} (a b : Array NQ N) (i : Usize) (x : NQ)
    (ha : canonical a) (hx : Canon x) (run : Array.update a i x=ok b) : canonical b :=
  (FIw_ArrayValue.update a b i x (bound a b i x run) ha hx run).1
/-- Exact stored value, for every address, including out-of-range lookups. -/
theorem value {N : Usize} (a b : Array NQ N) (i : Usize) (x : NQ)
    (run : Array.update a i x=ok b) (j : Nat) :
    FIv_NativeArray.value b j = if i.val=j then decode x else FIv_NativeArray.value a j := by
  have hi : i.val<a.val.length := by simpa only [a.property] using bound a b i x run
  unfold Array.update at run
  split at run
  · cases run
  · have same := Result.ok.inj run
    subst b
    by_cases he : i.val=j
    · subst j
      simp only [FIv_NativeArray.value,List.getElem?_set_self hi,↓reduceIte]
    · simp only [FIv_NativeArray.value,List.getElem?_set_ne he,he,↓reduceIte]
#print axioms bound
#print axioms canonical_write
#print axioms value
end AspisR1.FJa_ArrayUpdate
end
