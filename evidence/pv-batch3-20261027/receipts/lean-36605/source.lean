import PV_B3_SparseSet
import PV_B3_Forest_134_Funs
namespace PV_B3_MaskSparseStep
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Forest_134 PV_B3_SparseArray
set_option autoImplicit false

def block (p : Usize) : Usize := Usize.wrapping_shr p 4#u32
def bit (p : Usize) : U16 :=
  U16.wrapping_shl 1#u16 (UScalar.cast .U32 (p &&& 15#usize))
def mark (m : Nat → U16) (p : Usize) : Nat → U16 :=
  Function.update m (block p).val (m (block p).val ||| bit p)

theorem step (P C : Nat → U8) (M : Nat → U16) (i p c : Usize)
    (a b : U16) (np nc : U8)
    (hi : i < 136#usize)
    (hlink : Array.index_usize host_forest.MASK_LINKS i = ok (a,b))
    (ha : UScalar.cast .Usize a = p) (hb : UScalar.cast .Usize b = c)
    (hp : p < 1024#usize) (hc : c < 1024#usize)
    (hbp : host_forest.mask_endpoint_bump (P p.val) = ok (some np))
    (hbc : host_forest.mask_endpoint_bump (C c.val) = ok (some nc))
    (hmp : (block p).val < 64) (hmc : (block c).val < 64) :
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
      (array 1024#usize P) (array 1024#usize C) (array 64#usize M) i =
      ok (cont (array 1024#usize (Function.update P p.val np),
        array 1024#usize (Function.update C c.val nc),
        array 64#usize (mark (mark M p) c), Usize.wrapping_add i 1#usize)) := by
  unfold host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
  rw [if_pos hi, hlink]
  simp only [bind_tc_ok, ha, hb]
  rw [if_neg (not_le.mpr hp), index _ P p hp, hbp]
  simp only [bind_tc_ok]
  rw [PV_B3_SparseSet.mutable_index _ P p hp]
  simp only [bind_tc_ok]
  rw [if_neg (not_le.mpr hc), index _ C c hc, hbc]
  simp only [bind_tc_ok]
  rw [update _ C c hc]
  simp only [bind_tc_ok]
  change (do
    let v ← Array.index_usize (array 64#usize M) (block p)
    let m1 ← Array.update (array 64#usize M) (block p) (v ||| bit p)
    let w ← Array.index_usize m1 (block c)
    let m2 ← Array.update m1 (block c) (w ||| bit c)
    ok (cont (array 1024#usize (Function.update P p.val np),
      array 1024#usize (Function.update C c.val nc), m2,
      Usize.wrapping_add i 1#usize))) = _
  rw [index _ M _ hmp]
  simp only [bind_tc_ok]
  rw [update _ M _ hmp]
  simp only [bind_tc_ok]
  rw [index _ (mark M p) _ hmc]
  simp only [bind_tc_ok]
  rw [update _ (mark M p) _ hmc]
  rfl

#print axioms block
#print axioms bit
#print axioms mark
#print axioms step
end PV_B3_MaskSparseStep
