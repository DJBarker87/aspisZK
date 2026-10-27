import RPv_FJj_PointAdvance
import RPu_FJf_RawPointOuterFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_PointThird
open Aeneas Aeneas.Std Result
open FJf_PointBody (Factors Points)
open FJc_WeightQMBridge (SQ)

theorem value (points : Points) (p0 p1 p2 : Array SQ 10#usize)
    (hp0 : Array.index_usize points 0#usize=ok p0) (hc0 : FJc_WeightArray.canonical p0)
    (hp1 : Array.index_usize points 1#usize=ok p1) (hc1 : FJc_WeightArray.canonical p1)
    (hp2 : Array.index_usize points 2#usize=ok p2) (hc2 : FJc_WeightArray.canonical p2)
    (factors out : Factors) (hf : FJf_FactorArray.canon factors)
    (run : FIn_WeightsExtract.weights_new_loop0 {start:=0#usize,«end»:=3#usize}
      points factors=ok out) :
    (∀ row,out.val[2]?=some row → FJf_FactorArray.rowCanon row) ∧
    ∀ (d : Fin 5) (s : Fin 4),
      FJf_FactorArray.value out 2 d.val s.val=FJf_PointCell.point p2 d.val s := by
  obtain ⟨k0,cursor0,mid0,hn0,hm0,tail0⟩ :=
    FJj_PointAdvance.value points _ factors out (by change (0:Nat)<3;decide) run
  have pr0 := FIo_RangeNext.some_next _ cursor0 k0 hn0
  have ek0 : k0=0#usize := pr0.1
  subst k0
  have start0 : cursor0.start.val=1 := by
    have h := pr0.2.2.1
    change cursor0.start.val=0+1 at h
    exact h
  have end0 : cursor0.end.val=3 := by
    have h := congrArg UScalar.val pr0.2.1
    exact h
  have first := FJf_PointLoop.five points 0#usize p0 hp0 hc0 factors mid0 hf hm0
  obtain ⟨k1,cursor1,mid1,hn1,hm1,tail1⟩ :=
    FJj_PointAdvance.value points cursor0 mid0 out (by omega) tail0
  have pr1 := FIo_RangeNext.some_next cursor0 cursor1 k1 hn1
  have ek1 : k1=1#usize := by apply UScalar.eq_of_val_eq;rw [pr1.1];exact start0
  subst k1
  have start1 : cursor1.start.val=2 := by rw [pr1.2.2.1,start0]
  have second := FJf_PointLoop.five points 1#usize p1 hp1 hc1 mid0 mid1 first.1 hm1
  have end1 : cursor1.end.val=3 := by rw [pr1.2.1];exact end0
  obtain ⟨k2,cursor2,mid2,hn2,hm2,tail2⟩ :=
    FJj_PointAdvance.value points cursor1 mid1 out (by omega) tail1
  have pr2 := FIo_RangeNext.some_next cursor1 cursor2 k2 hn2
  have ek2 : k2=2#usize := by apply UScalar.eq_of_val_eq;rw [pr2.1];exact start1
  subst k2
  have start2 : cursor2.start.val=3 := by rw [pr2.2.2.1,start1]
  have third := FJf_PointLoop.five points 2#usize p2 hp2 hc2 mid1 mid2 second.1 hm2
  have frame := FJf_PointOuterFrame.loop points 2 cursor2 mid2 out (by omega) tail2
  have raw := FJf_RawPointOuterFrame.loop points 2 cursor2 mid2 out (by omega) tail2
  constructor
  · intro row hr
    apply third.1 row
    rw [raw] at hr
    exact List.mem_of_getElem? hr
  · intro d s
    rw [frame d.val s.val]
    have hv := third.2 2 d.val s
    simpa only [show (2#usize).val=2 from by decide,eq_self,true_and,if_pos d.isLt] using hv
#print axioms value
end AspisR1.FJm_PointThird
end
