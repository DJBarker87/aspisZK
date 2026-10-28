import R1Z.BuilderBankRange
import R1Z.BuilderRecordsArray

set_option autoImplicit false
namespace R1Z.BuilderBankStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder
open BuilderBankCells
attribute [local instance] Classical.propDecidable
abbrev Bank := Array U32 16384#usize

def stableValue (pt : Parts) (k : Nat) : U32 :=
  if LateRow k then 0#u32 else cell pt (k/1024) (k%1024)
def lateValue (pt : Parts) (k : Nat) : U32 :=
  if LateRow k then cell pt (k/1024) (k%1024) else 0#u32

theorem late_cell (pt : Parts) (k : Nat) (hk : k < 16384) (h : LateRow k) :
    cell pt (k/1024) (k%1024) =
      (pt.blocks.val[k%1024/16]!).val[(k%1024%16)*16+k/1024]! := by
  unfold LateRow at h
  rw [cell, if_pos (by omega), if_pos (by omega)]

theorem step (pt : Parts) (hblocks : pt.blocks.val.length = 57) (stable late : Bank)
    (iter after : core.ops.range.Range Usize) (k : Usize) (hk : k.val < 16384)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some k,after)) :
    merged_banks_loop iter pt stable late =
      merged_banks_loop after pt
        (stable.set k (stableValue pt k.val)) (late.set k (lateValue pt k.val)) := by
  rw [merged_banks_loop,next]
  simp only [bind_tc_ok]
  rw [BuilderBankShape.late_row]
  simp only [bind_tc_ok]
  by_cases hlate : LateRow k.val
  · have hrows := hlate
    unfold LateRow at hrows
    simp only [hlate,decide_true,if_true,stableValue,lateValue]
    rw [update_ok stable k _ (by simpa using hk)]
    simp only [bind_tc_ok]
    obtain ⟨r,hr,vr⟩ := rem1024 k
    rw [hr]
    simp only [bind_tc_ok]
    obtain ⟨q,hq,vq⟩ := UScalar.div_spec r (y := 16#usize) (by simp)
    rw [hq]
    simp only [bind_tc_ok]
    have vr' : r.val = k.val%1024 := by simpa using vr
    have vq' : q.val = k.val%1024/16 := by simpa [vr'] using vq
    rw [vec_index _ q (by rw [hblocks,vq']; omega)]
    simp only [bind_tc_ok]
    obtain ⟨m,hm,vm⟩ := WP.spec_imp_exists (UScalar.rem_spec r (y := 16#usize) (by simp))
    rw [hm]
    simp only [bind_tc_ok,lift]
    obtain ⟨c,hc,vc⟩ := UScalar.div_spec k (y := 1024#usize) (by simp)
    rw [hc]
    simp only [bind_tc_ok,lift]
    have vm' : m.val = k.val%1024%16 := by simpa [vr'] using vm
    have vc' : c.val = k.val/1024 := by simpa using vc
    have vprod : (Usize.wrapping_mul m 16#usize).val = (k.val%1024%16)*16 := by
      rw [umul _ _ (by simp; omega)]; simp only [vm',UScalar.ofNatCore_val_eq]
    have vsum : (Usize.wrapping_add (Usize.wrapping_mul m 16#usize) c).val =
        (k.val%1024%16)*16+k.val/1024 := by
      rw [uadd _ _ (by rw [vprod,vc']; omega),vprod,vc']
    rw [index_ok _ _ (by rw [vsum]; simp; omega)]
    simp only [bind_tc_ok]
    rw [update_ok late k _ (by simpa using hk)]
    simp only [bind_tc_ok,vsum,vq']
    rw [late_cell pt k.val hk hlate]
  · simp only [hlate,decide_false,Bool.false_eq_true,if_false,stableValue,lateValue]
    obtain ⟨c,hc,vc⟩ := UScalar.div_spec k (y := 1024#usize) (by simp)
    rw [hc]
    simp only [bind_tc_ok]
    obtain ⟨r,hr,vr⟩ := rem1024 k
    rw [hr]
    simp only [bind_tc_ok]
    rw [BuilderBankCells.copy_cell pt hblocks c r (by simpa [vr] using Nat.mod_lt k.val (by decide : 0 < 1024))]
    simp only [bind_tc_ok]
    rw [update_ok stable k _ (by simpa using hk)]
    simp only [bind_tc_ok]
    rw [update_ok late k _ (by simpa using hk)]
    simp only [bind_tc_ok]
    have vc' : c.val = k.val/1024 := by simpa using vc
    simp only [vc',vr]

#print axioms late_cell
#print axioms step
end R1Z.BuilderBankStep
