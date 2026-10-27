import RPv_FJr_LibraBodyValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraOne
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide qm)
open FJr_LibraFactors (FK FE)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (extra : Array NQ 2#usize)
    (ca0 : FIo_WideValues.Canon a0) (ca1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (ce : ∀ q∈extra.val,FIo_QMValues.Canon q)
    (iter cursorOut : FIo_RangeNext.Range) (weights out : Array NE 4#usize)
    (cw : FIo_ArrayCanon.Holds weights) (start : iter.start=1#usize)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=
      ok (.cont (cursorOut,out))) :
    let q := algebraMap FK FE (FJf_QMArray.value extra 1)
    let low := FJm_LibraModel.low q (decodeWide (wide a0))
    let t := FJm_LibraModel.term q (decodeWide (wide a1))
    cursorOut.end=iter.end ∧ cursorOut.start.val=2 ∧ FIo_ArrayCanon.Holds out ∧
      ∀ j,FIp_ArrayValue.value out j=
        if j=1 then FIp_ArrayValue.value weights 1+low*(RoundPairing.quarter*decodeWide (wide a1))
        else if j=2 then low*(t 0+t 1+t 2+t 3)*q^4
        else if j=3 then low*(t 0+t 1)*q^20
        else FIp_ArrayValue.value weights j := by
  obtain ⟨side,cursor,q,low,first2,first3,all,i3,q4,q16,
    sideEq,endEq,step,more,hq,cl,c2,c3,call,c4,c16,idx,v4,v16,vl,v2,v3,va,hfinish⟩ :=
    FJr_LibraBodyValues.value a0 a1 ap0 ap1 extra ca0 ca1 hp0 hp1 ce iter cursorOut weights out run
  have sideOne : side=1#usize := sideEq.trans start
  rw [sideOne] at hfinish hq
  have cp := FIp_PowersValue.powers 4#usize a1 ap1 ca1 hp1
  have fin := FJm_LibraFinishOne.value low first2 first3 all i3 q4 q16 ap1 weights out cursor cursorOut
    cl c2 call cp.1 cw c4 c16 hfinish
  have qvalue : FJf_QMArray.value extra 1=decodeQM (qm q) := FJf_QMArray.read extra 1#usize q hq
  have a1value : FIp_ArrayValue.value ap1 i3.val=decodeWide (wide a1) := by
    rw [idx,cp.2 1 (by change (1:Nat)<4;decide),pow_one]
  have q20 : algebraMap FK FE (decodeQM (qm q16)*decodeQM (qm q4))=
      (algebraMap FK FE (decodeQM (qm q)))^20 := by
    rw [v16,v4,map_mul,map_pow,map_pow,←pow_add]
  dsimp only
  refine ⟨fin.1 ▸ endEq,?_,fin.2.1,?_⟩
  · rw [fin.1,step,start];rfl
  · intro j
    rw [fin.2.2 j,a1value,vl,v2,va,q20,v4,map_pow,←qvalue]

#print axioms value
end AspisR1.FJr_LibraOne
end
