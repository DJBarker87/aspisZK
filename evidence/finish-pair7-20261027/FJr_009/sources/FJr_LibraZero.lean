import FJr_LibraBodyValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraZero
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
    (cw : FIo_ArrayCanon.Holds weights) (start : iter.start=0#usize)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=
      ok (.cont (cursorOut,out))) :
    let q := algebraMap FK FE (FJf_QMArray.value extra 0)
    let low := FJm_LibraModel.low q (decodeWide (wide a0))
    let t := FJm_LibraModel.term q (decodeWide (wide a1))
    cursorOut.end=iter.end ∧ cursorOut.start.val=1 ∧ FIo_ArrayCanon.Holds out ∧
      ∀ j,FIp_ArrayValue.value out j=
        if j=0 then low*(t 0+t 1+t 2+t 3)
        else if j=1 then low*(t 0+t 1+t 2)*q^16
        else FIp_ArrayValue.value weights j := by
  obtain ⟨side,cursor,q,low,first2,first3,all,i3,q4,q16,
    sideEq,endEq,step,more,hq,cl,c2,c3,call,c4,c16,idx,v4,v16,vl,v2,v3,va,hfinish⟩ :=
    FJr_LibraBodyValues.value a0 a1 ap0 ap1 extra ca0 ca1 hp0 hp1 ce iter cursorOut weights out run
  have sideZero : side=0#usize := sideEq.trans start
  subst side
  have fin := FJm_LibraFinishZero.value low first2 first3 all i3 q4 q16 ap1 weights out cursor cursorOut
    cl c3 call cw hfinish
  have qvalue : FJf_QMArray.value extra 0=decodeQM (qm q) := FJf_QMArray.read extra 0#usize q hq
  dsimp only
  refine ⟨fin.1 ▸ endEq,?_,fin.2.1,?_⟩
  · rw [fin.1,step,start];rfl
  · intro j
    rw [fin.2.2 j,vl,v3,va,v16,map_pow,←qvalue]

#print axioms value
end AspisR1.FJr_LibraZero
end
