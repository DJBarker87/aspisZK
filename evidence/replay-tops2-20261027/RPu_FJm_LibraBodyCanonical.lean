import RPu_FJm_LibraBodyCut
import RPu_FJm_LibraPowerValues
import RPu_FJm_LibraTermValue
import RPu_FJm_LibraTotals
import RPu_FJm_LibraFinishZero
import RPu_FJm_LibraFinishOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraBodyCanonical
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)

theorem value (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter cursorOut : FIo_RangeNext.Range)
    (weights out : Weights) (he : iter.end.val=2)
    (cp0 : FIo_ArrayCanon.Holds ap0) (cp1 : FIo_ArrayCanon.Holds ap1)
    (ce : ∀ q∈extra.val,FIo_QMValues.Canon q) (cw : FIo_ArrayCanon.Holds weights)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=
      ok (.cont (cursorOut,out))) :
    cursorOut.end=iter.end ∧ cursorOut.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
      FIo_ArrayCanon.Holds out := by
  obtain ⟨side,cursor,base,high,q4,q16,low,i0,i1,i2,i3,t0,t1,t2,t3,first2,first3,all,
    hn,hpowers,hlow,ht0,ht1,ht2,ht3,htotals,hfinish⟩ :=
    FJm_LibraBodyCut.reached ap0 ap1 extra iter cursorOut weights out run
  have pr := FIo_RangeNext.some_next iter cursor side hn
  obtain ⟨q,hq,cq,cb,ch,vb,vh,c4,c16,v4,v16⟩ := FJm_LibraPowerValues.value extra side ce base high q4 q16 hpowers
  have vl := FJg_ScalarValue.value ap0 base cp0 low hlow
  have vt0 := FJm_LibraTermValue.value ap1 high 0#usize i0 t0 cp1 ht0
  have vt1 := FJm_LibraTermValue.value ap1 high 1#usize i1 t1 cp1 ht1
  have vt2 := FJm_LibraTermValue.value ap1 high 2#usize i2 t2 cp1 ht2
  have vt3 := FJm_LibraTermValue.value ap1 high 3#usize i3 t3 cp1 ht3
  have ct : FIo_ArrayCanon.Holds (Array.make 4#usize [t0,t1,t2,t3]) := by
    intro x hx
    change x∈[t0,t1,t2,t3] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact vt0.2.1
    · exact vt1.2.1
    · exact vt2.2.1
    · exact vt3.2.1
  have totals := FJm_LibraTotals.value (Array.make 4#usize [t0,t1,t2,t3]) ct first2 first3 all htotals
  have sideBound : side.val < 2 := by rw [pr.1];omega
  have sideCases : side=0#usize ∨ side=1#usize := by
    have hv : side.val=0 ∨ side.val=1 := by omega
    rcases hv with hv|hv
    · left;apply UScalar.eq_of_val_eq;exact hv
    · right;apply UScalar.eq_of_val_eq;exact hv
  rcases sideCases with rfl|rfl
  · have fin := FJm_LibraFinishZero.value low first2 first3 all i3 q4 q16 ap1 weights out cursor cursorOut
      vl.1 totals.2.1 totals.2.2.1 cw hfinish
    rw [fin.1]
    exact ⟨pr.2.1,pr.2.2.1,pr.2.2.2,fin.2.1⟩
  · have fin := FJm_LibraFinishOne.value low first2 first3 all i3 q4 q16 ap1 weights out cursor cursorOut
      vl.1 totals.1 totals.2.2.1 cp1 cw c4 c16 hfinish
    rw [fin.1]
    exact ⟨pr.2.1,pr.2.2.1,pr.2.2.2,fin.2.1⟩
#print axioms value
end AspisR1.FJm_LibraBodyCanonical
end
