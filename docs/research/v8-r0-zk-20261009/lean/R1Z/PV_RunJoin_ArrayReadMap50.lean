import R1Z.PV_RunJoin_WeightMap46
import R1Z.PV_RunJoin_ClaimList48
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ArrayReadMap50
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (amap)

theorem array {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (i : Usize) (hi : i.val<n.val) :
    Array.index_usize (amap f a) i=ok (f (a.val[i.val]'(by rw [a.property];exact hi))) := by
  rw [PV_RunJoin_WeightMap46.index,ProverCommitArrayIndex25.array_index_usize_ok a i hi]
  rfl

theorem slice {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (i : Usize) (hi : i.val<n.val) :
    Slice.index_usize (Array.to_slice (amap f a)) i=ok (f (a.val[i.val]'(by rw [a.property];exact hi))) := by
  rw [PV_RunJoin_ClaimList48.read _ i (by simp only [Array.to_slice,amap,List.length_map,a.property];exact hi)]
  simp only [Array.to_slice,amap,List.getElem_map]
#print axioms array
#print axioms slice
end R1Z.PV_RunJoin_ArrayReadMap50
