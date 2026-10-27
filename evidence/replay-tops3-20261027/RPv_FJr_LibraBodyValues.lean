import RPv_FJr_LibraFactors
import RPv_FJm_LibraBodyCut
import RPv_FJm_LibraPowerValues
import RPv_FJm_LibraTotals
import RPv_FJm_LibraFinishZero
import RPv_FJm_LibraFinishOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraBodyValues
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide qm)
open FJr_LibraFactors (FK FE)
attribute [local irreducible] QuadraticAlgebra.instInv

/-- Actual reached body, with all contractions on its own extra read. -/
theorem value (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (extra : Array NQ 2#usize)
    (ca0 : FIo_WideValues.Canon a0) (ca1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (ce : ∀ q∈extra.val,FIo_QMValues.Canon q)
    (iter cursorOut : FIo_RangeNext.Range) (weights out : Array NE 4#usize)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=
      ok (.cont (cursorOut,out))) :
    ∃ (side : Usize) (cursor : FIo_RangeNext.Range) (q : NQ)
      (low first2 first3 all : NE) (i3 : Usize) (q4 q16 : NQ),
      side=iter.start ∧ cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧
      iter.start.val < iter.end.val ∧ Array.index_usize extra side=ok q ∧
      FIo_WideValues.Canon low ∧ FIo_WideValues.Canon first2 ∧
      FIo_WideValues.Canon first3 ∧ FIo_WideValues.Canon all ∧
      FIo_QMValues.Canon q4 ∧ FIo_QMValues.Canon q16 ∧ i3.val=1 ∧
      decodeQM (qm q4)=decodeQM (qm q)^4 ∧ decodeQM (qm q16)=decodeQM (qm q)^16 ∧
      decodeWide (wide low)=FJm_LibraModel.low (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a0)) ∧
      decodeWide (wide first2)=FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 0+
        FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 1 ∧
      decodeWide (wide first3)=FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 0+
        FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 1+
        FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 2 ∧
      decodeWide (wide all)=FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 0+
        FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 1+
        FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 2+
        FJm_LibraModel.term (algebraMap FK FE (decodeQM (qm q))) (decodeWide (wide a1)) 3 ∧
      FJm_LibraStages.finish side low i3 first2 first3 all q4 q16 ap1 weights cursor=
        ok (.cont (cursorOut,out)) := by
  obtain ⟨side,cursor,base,high,q4,q16,low,i0,i1,i2,i3,t0,t1,t2,t3,first2,first3,all,
    hn,hpowers,hlow,ht0,ht1,ht2,ht3,htotals,hfinish⟩ :=
    FJm_LibraBodyCut.reached ap0 ap1 extra iter cursorOut weights out run
  have pr := FIo_RangeNext.some_next iter cursor side hn
  obtain ⟨q,hq,cq,cb,ch,vb,vh,c4,c16,v4,v16⟩ := FJm_LibraPowerValues.value extra side ce base high q4 q16 hpowers
  have vl := FJr_LibraFactors.low a0 ap0 base (decodeQM (qm q)) ca0 hp0 vb low hlow
  have vt0 := FJr_LibraFactors.term a1 ap1 high (decodeQM (qm q)) ca1 hp1 vh 0 0#usize i0 t0 rfl ht0
  have vt1 := FJr_LibraFactors.term a1 ap1 high (decodeQM (qm q)) ca1 hp1 vh 1 1#usize i1 t1 rfl ht1
  have vt2 := FJr_LibraFactors.term a1 ap1 high (decodeQM (qm q)) ca1 hp1 vh 2 2#usize i2 t2 rfl ht2
  have vt3 := FJr_LibraFactors.term a1 ap1 high (decodeQM (qm q)) ca1 hp1 vh 3 3#usize i3 t3 rfl ht3
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
  have e0 : FIp_ArrayValue.value (Array.make 4#usize [t0,t1,t2,t3]) 0=decodeWide (wide t0) := rfl
  have e1 : FIp_ArrayValue.value (Array.make 4#usize [t0,t1,t2,t3]) 1=decodeWide (wide t1) := rfl
  have e2 : FIp_ArrayValue.value (Array.make 4#usize [t0,t1,t2,t3]) 2=decodeWide (wide t2) := rfl
  have e3 : FIp_ArrayValue.value (Array.make 4#usize [t0,t1,t2,t3]) 3=decodeWide (wide t3) := rfl
  refine ⟨side,cursor,q,low,first2,first3,all,i3,q4,q16,pr.1,pr.2.1,pr.2.2.1,pr.2.2.2,hq,
    vl.1,totals.1,totals.2.1,totals.2.2.1,c4,c16,vt3.1,v4,v16,vl.2,?_,?_,?_,hfinish⟩
  · rw [totals.2.2.2.1,e0,e1,vt0.2.2,vt1.2.2]
  · rw [totals.2.2.2.2.1,e0,e1,e2,vt0.2.2,vt1.2.2,vt2.2.2]
  · rw [totals.2.2.2.2.2,e0,e1,e2,e3,vt0.2.2,vt1.2.2,vt2.2.2,vt3.2.2]

#print axioms value
end AspisR1.FJr_LibraBodyValues
end
