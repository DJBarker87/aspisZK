import R1Z.PV_RunJoin_NativePowerCarrier66
import R1Z.ProverRwP6ArrayRead
import R1Z.ProverRwP6ArrayMap
import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerArray66
open Aeneas Aeneas.Std Result PV_RunJoin_NativePowerCarrier66
open PV_B2_F_ConstructorCarrier (amap)
def image {N : Usize} (out : Array W N) := amap toS out
theorem read {N : Usize} (out : Array W N) (i : Usize) (hi : i.val<N.val) :
    ∃ v, Array.index_mut_usize out i=ok (v,Aeneas.Std.Array.set out i) ∧
      Array.index_mut_usize (image out) i=ok (toS v,Aeneas.Std.Array.set (image out) i) := by
  obtain ⟨v,hv⟩ := ProverRwP6ArrayRead.read out i hi
  have hn : Array.index_usize (image out) i=ok (toS v) := by
    rw [image,PV_RunJoin_WeightMap46.index,hv]
    rfl
  refine ⟨v,?_,?_⟩ <;> unfold Array.index_mut_usize
  · rw [hv];rfl
  · rw [hn];rfl
theorem set {N : Usize} (out : Array W N) (i : Usize) (p : W) :
    image (Aeneas.Std.Array.set out i p)=Aeneas.Std.Array.set (image out) i (toS p) :=
  ProverRwP6ArrayMap.set_map toS out i p
#print axioms read
#print axioms set
end R1Z.PV_RunJoin_NativePowerArray66
