import S9NativeS3CoefficientBodyV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9NativeS3CoefficientLoopV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3CoefficientBodyV1 (W R C toOld)
open AspisR1S9NativeArrayCanonicalV1 (ReadsCanonical)
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m;next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,h⟩

private theorem native_done_old (f : Slice U8) (r : R) (c out : C)
    (h : weights.s2_grouped_inactive_pair_loop0.body f r c=.ok (.done out)) :
    AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair_loop0.body
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations f r (toOld c)=
      .ok (.done (toOld out)) := by
  unfold weights.s2_grouped_inactive_pair_loop0.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,r1⟩
  cases opt with
  | none =>
    have he : c=out := ControlFlow.done.inj (Result.ok.inj h)
    subst out
    unfold AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair_loop0.body
    simp only [hn,bind_tc_ok]
    have htail :
        (Result.ok (ControlFlow.done (toOld c)) :
          Result (ControlFlow (R × Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 12#usize)
            (Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 12#usize)))=
        Result.ok (ControlFlow.done (toOld c)) := rfl
    exact htail
  | some j =>
    obtain ⟨code,hcode,h⟩ := bind_success _ _ _ h
    obtain ⟨group,hgroup,h⟩ := bind_success _ _ _ h
    obtain ⟨old,hold,h⟩ := bind_success _ _ _ h
    obtain ⟨value,hfield,h⟩ := bind_success _ _ _ h
    obtain ⟨total,hadd,h⟩ := bind_success _ _ _ h
    obtain ⟨updated,hupdate,h⟩ := bind_success _ _ _ h
    cases h

/-- Accepted native64 accumulation simulates the SAME old source loop on the
SAME mapped coefficient array. No old read, old loop success, field canonical
input or coefficient-meaning conclusion is supplied as a premise. -/
theorem native_coefficient_loop_success_old
    (f : Slice U8) (iter : R) (a out : C)
    (hbytes : 2048 ≤ f.val.length)
    (hend : iter.end.val=64) (hstart : iter.start.val ≤ 64)
    (ha : ReadsCanonical a)
    (hrun : weights.s2_grouped_inactive_pair_loop0 iter f a=.ok out) :
    AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair_loop0
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations iter f (toOld a)=
      .ok (toOld out) := by
  let step := fun s : R × C => weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2
  let oldStep := fun s : R × Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 12#usize =>
    AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair_loop0.body
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations f s.1 s.2
  let inv := fun s : R × C => s.1.end.val=64 ∧ s.1.start.val≤64 ∧ ReadsCanonical s.2 ∧
    Aeneas.Std.loop oldStep (iter,toOld a)=Aeneas.Std.loop oldStep (s.1,toOld s.2)
  let post := fun result : C => Aeneas.Std.loop oldStep (iter,toOld a)=.ok (toOld result)
  let measure := fun s : R × C => s.1.end.val-s.1.start.val
  have hd : ∀ s result,inv s → step s=.ok (.done result) → post result := by
    rintro ⟨r,c⟩ result ⟨he,hs,hc,hprefix⟩ hb
    have hold : oldStep (r,toOld c)=.ok (.done (toOld result)) := native_done_old f r c result hb
    change Aeneas.Std.loop oldStep (iter,toOld a)=.ok (toOld result)
    change Aeneas.Std.loop oldStep (iter,toOld a)=Aeneas.Std.loop oldStep (r,toOld c) at hprefix
    rw [hprefix,Aeneas.Std.loop.eq_def,hold] <;> rfl
  have hc : ∀ s s',inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,c⟩ ⟨r1,c1⟩ ⟨he,hs,hcan,hprefix⟩ hb
    change r.end.val=64 at he
    change r.start.val≤64 at hs
    obtain ⟨j,code,group,old,value,total,hn,hcode,hgroup,hold,hfield,hadd,hupdate⟩ :=
      AspisR1S9S2CoefficientsCanonicalV1.body_cont_source f r r1 c c1 hb
    obtain ⟨hj,hlt,hadvance,hend1⟩ :=
      AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds r r1 j hn
    have he1 : r1.end.val=64 := by rw [hend1];exact he
    have hs1 : r1.start.val≤64 := by
      have hv : j.val=r.start.val := congrArg (fun x : Usize => x.val) hj
      omega
    have co := hcan group old hold
    have hfit : (j.val+1)*32 ≤ f.val.length := by omega
    have cv := AspisR1S9NativeS3CoefficientBodyV1.native_field_success_canonical_of_fit f j value hfit hfield
    have ct := (AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded old value total co cv hadd).1
    have hg := AspisR1S9ConstructorV3Loop2InnerCanonicalV1.index_success_bound c group old hold
    have cc := AspisR1S9NativeArrayCanonicalV1.accepted_update_preserves_canonical
      c c1 group total hg hcan ct hupdate
    have holdBody : oldStep (r,toOld c)=.ok (.cont (r1,toOld c1)) :=
      AspisR1S9NativeS3CoefficientBodyV1.native_coefficient_cont_old_body
        f r r1 c c1 hbytes (by omega) hcan hb
    have htail : Aeneas.Std.loop oldStep (r,toOld c)=Aeneas.Std.loop oldStep (r1,toOld c1) := by
      rw [Aeneas.Std.loop.eq_def,holdBody] <;> rfl
    change r1.end.val=64 ∧ r1.start.val≤64 ∧ ReadsCanonical c1 ∧
      Aeneas.Std.loop oldStep (iter,toOld a)=Aeneas.Std.loop oldStep (r1,toOld c1)
    exact ⟨he1,hs1,cc,hprefix.trans htail⟩
  have hm : ∀ s s',step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,c⟩ ⟨r1,c1⟩ hb
    obtain ⟨j,code,group,old,value,total,hn,hcode,hgroup,hold,hfield,hadd,hupdate⟩ :=
      AspisR1S9S2CoefficientsCanonicalV1.body_cont_source f r r1 c c1 hb
    obtain ⟨hj,hlt,hadvance,hend1⟩ :=
      AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds r r1 j hn
    change r1.end.val-r1.start.val < r.end.val-r.start.val
    rw [hend1,hadvance]
    have hv : j.val=r.start.val := congrArg (fun x : Usize => x.val) hj
    omega
  have hi : inv (iter,a) := ⟨hend,hstart,ha,rfl⟩
  have hl : Aeneas.Std.loop step (iter,a)=.ok out := hrun
  have hp := AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure inv post hd hc hm _ out hi hl
  exact hp

#print axioms native_coefficient_loop_success_old
end AspisR1S9NativeS3CoefficientLoopV1
