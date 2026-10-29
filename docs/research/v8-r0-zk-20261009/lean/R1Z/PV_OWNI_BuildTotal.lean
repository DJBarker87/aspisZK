import R1Z.PV_OWNI_WeightTotal
import R1Z.PV_OWNI_MapMLength
set_option autoImplicit false
namespace R1Z.PV_OWNI_BuildTotal
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def entries (point : List Q) (width trailing suffix : Nat) : List (Nat × Q) :=
 (List.range (2^width)).map fun pref=>
 (PV_RDB2D_SparseAddress.row pref trailing suffix,
  ((point.take width).foldl (PV_OWNI_WeightTotal.step width pref) (ops.one,0)).1)

theorem mapM_pure {A B : Type} (xs : List A) (f : A → B) :
 xs.mapM (fun x=>ok (f x))=ok (xs.map f) := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  simp only [List.mapM_cons,List.map_cons,ih,bind_tc_ok]
  rfl

theorem result (point : List Q) (width trailing suffix : Nat) :
 PV_RDB2D_SparseWeights.build ops point width trailing suffix=ok (entries point width trailing suffix) := by
 unfold PV_RDB2D_SparseWeights.build
 simp only [PV_OWNI_WeightTotal.source_result,bind_tc_ok]
 exact mapM_pure _ _

theorem cardinality (point : List Q) (width trailing suffix : Nat) :
 (entries point width trailing suffix).length=2^width := by
 have h:=PV_OWNI_MapMLength.length _ _ _ (result point width trailing suffix)
 simpa only [List.length_range] using h
#print axioms mapM_pure
#print axioms result
#print axioms cardinality
end R1Z.PV_OWNI_BuildTotal
