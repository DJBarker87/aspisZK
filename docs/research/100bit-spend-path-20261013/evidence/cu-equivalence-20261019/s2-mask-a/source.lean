import CuSavingsS2SourceMaskFlag
import CuSavingsS2MaskBits
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceMask
open Aeneas Aeneas.Std Result ControlFlow AspisR1S2Groups
open OccupancyRangeTraversal
variable [Shared]

theorem body_step (w : Weights) (j : Usize) (m mask : U16) (iter next : Range)
    (hw : w.variant=transport.Variant.S2) (hj : j.val<64) (hs : iter.start.val<16)
    (hm : m.val=CuSavingsS2Tables.masks.getD (CuSavingsS2Tables.groupValue ⟨j.val,hj⟩) 0)
    (hp : mask.val=m.val%2^iter.start.val)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start,next)) :
    ∃ value : U16,
      old.grouped_inactive_pair_loop0_loop0.body w j iter mask = .ok (.cont (next,value)) ∧
      value.val=m.val%2^(iter.start.val+1) := by
  have hf := CuSavingsS2SourceMaskFlag.source_flag w j iter.start m hw hj hs hm
  obtain ⟨one,ho,hov,_⟩ := WP.spec_imp_exists (U16.ShiftLeft_spec 1#u16 iter.start hs)
  have hfit : (1#u16).val <<< iter.start.val < U16.size := by
    have h1 : (1#u16).val=1 := by decide
    rw [h1,Nat.shiftLeft_eq,Nat.one_mul]
    change (2:Nat)^iter.start.val < 2^16
    exact Nat.pow_lt_pow_right (by decide) hs
  rw [Nat.mod_eq_of_lt hfit] at hov
  have hone : one.val=2^iter.start.val := by simpa [Nat.shiftLeft_eq] using hov
  have factor : old.grouped_inactive_pair_loop0_loop0.body w j iter mask = (do
      let b ← CuSavingsS2SourceMaskFlag.flag w j iter.start
      if b then
        let bit ← 1#u16 <<< iter.start
        .ok (.cont (next,mask ||| bit))
      else .ok (.cont (next,mask))) := by
    simp only [old.grouped_inactive_pair_loop0_loop0.body,hn,bind_tc_ok]
    change (do
      let p ← 16#usize*j
      let i ← p+iter.start
      let q ← Weights.raw w 0#usize i
      let b ← field.QM31.Insts.CoreCmpPartialEqQM31.eq q field.QM31.ONE
      if b then
        let bit ← 1#u16 <<< iter.start
        Result.ok (ControlFlow.cont (β:=U16) (next,mask ||| bit))
      else Result.ok (ControlFlow.cont (β:=U16) (next,mask))) = _
    simp only [CuSavingsS2SourceMaskFlag.flag,bind_assoc_eq]
  refine ⟨if m.val.testBit iter.start.val then mask ||| one else mask,?_,?_⟩
  · rw [factor,hf,bind_tc_ok]
    cases hb : m.val.testBit iter.start.val <;> simp only [hb,ho,bind_tc_ok,Bool.false_eq_true,if_false,if_true]
  · have he := CuSavingsS2MaskBits.partial_step m.val iter.start.val
    cases hb : m.val.testBit iter.start.val <;>
      simpa only [hb,Bool.false_eq_true,if_false,if_true,UScalar.val_or,hp,hone] using he

theorem loop_source (fuel : Nat) (w : Weights) (j : Usize) (m mask : U16) (iter : Range)
    (hw : w.variant=transport.Variant.S2) (hj : j.val<64)
    (hm : m.val=CuSavingsS2Tables.masks.getD (CuSavingsS2Tables.groupValue ⟨j.val,hj⟩) 0)
    (hp : mask.val=m.val%2^iter.start.val)
    (he : iter.end.val=16) (hi : iter.start.val≤16) (hf : 16-iter.start.val=fuel) :
    old.grouped_inactive_pair_loop0_loop0 iter w j mask = .ok m := by
  induction fuel generalizing iter mask with
  | zero =>
    have hn := next_done iter (by omega)
    have hstart : iter.start.val=16 := by omega
    have hmfit : m.val<2^16 := m.bv.isLt
    have hmask : mask=m := UScalar.eq_of_val_eq (by rw [hp,hstart,Nat.mod_eq_of_lt hmfit])
    subst mask
    unfold old.grouped_inactive_pair_loop0_loop0
    rw [loop]
    simp only [old.grouped_inactive_pair_loop0_loop0.body,hn,bind_tc_ok]
    rfl
  | succ fuel ih =>
    obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
    obtain ⟨value,hvalue,hv⟩ := body_step w j m mask iter next hw hj (by omega) hm hp hn
    have hp1 : value.val=m.val%2^next.start.val := by rw [hinc];exact hv
    have hrec := ih value next hp1 (by rw [hend];exact he) (by omega) (by omega)
    unfold old.grouped_inactive_pair_loop0_loop0
    rw [loop]
    dsimp only
    rw [hvalue]
    exact hrec

theorem source_mask (w : Weights) (j : Usize) (m : U16)
    (hw : w.variant=transport.Variant.S2) (hj : j.val<64)
    (hm : m.val=CuSavingsS2Tables.masks.getD (CuSavingsS2Tables.groupValue ⟨j.val,hj⟩) 0) :
    old.grouped_inactive_pair_loop0_loop0 {start:=0#usize,«end»:=16#usize} w j 0#u16 = .ok m := by
  apply loop_source 16 w j m 0#u16 _ hw hj hm
  · have hz : (0#usize).val=0 := by scalar_tac
    simp only [hz,Nat.pow_zero,Nat.mod_one]
    rfl
  · scalar_tac
  · scalar_tac
  · scalar_tac

#print axioms body_step
#print axioms loop_source
#print axioms source_mask
end AspisR1.CuSavingsS2SourceMask
