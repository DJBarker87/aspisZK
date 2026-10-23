import S9S2CoefficientsCanonicalV1
import S9S2WeightCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9S2InactiveCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeArrayCanonicalV1
abbrev R := core.ops.range.Range Usize
abbrev Low := Array W 16#usize
abbrev Coefficients := Array W 12#usize
private theorem bind_success {X Y : Type} (m : Result X) (next : X → Result Y) (out : Y)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem outer_body_cont_source (low : Low) (coefficients : Coefficients)
    (iter iterOut : R) (pair out : W)
    (h : weights.s2_grouped_inactive_pair_loop1.body low coefficients iter pair=
      .ok (.cont (iterOut,out))) :
    ∃ (group : Usize) (weight coefficient product : W),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some group,iterOut) ∧
      weights.s2_grouped_inactive_pair_loop1_loop0 {start:=0#usize,«end»:=16#usize} low group
        aspis_core.field.wide_exact.WideExact.ZERO=.ok weight ∧
      Array.index_usize coefficients group=.ok coefficient ∧
      aspis_core.field.wide_exact.WideExact.mul coefficient weight=.ok product ∧
      aspis_core.field.wide_exact.WideExact.add pair product=.ok out := by
  unfold weights.s2_grouped_inactive_pair_loop1.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some group =>
    obtain ⟨weight,hw,h⟩ := bind_success _ _ _ h
    obtain ⟨coefficient,hc,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨total,ha,h⟩ := bind_success _ _ _ h
    have he := ControlFlow.cont.inj (Result.ok.inj h)
    cases he
    exact ⟨group,weight,coefficient,product,hn,hw,hc,hm,ha⟩

theorem outer_body_done_same (low : Low) (coefficients : Coefficients)
    (iter : R) (pair out : W)
    (h : weights.s2_grouped_inactive_pair_loop1.body low coefficients iter pair=.ok (.done out)) :
    out=pair := by
  unfold weights.s2_grouped_inactive_pair_loop1.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => exact (ControlFlow.done.inj (Result.ok.inj h)).symm
  | some group =>
    obtain ⟨weight,hw,h⟩ := bind_success _ _ _ h
    obtain ⟨coefficient,hc,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨total,ha,h⟩ := bind_success _ _ _ h
    cases h

theorem outer_loop_success_canonical (low : Low) (coefficients : Coefficients)
    (iter : R) (pair out : W) (hlow : ReadsCanonical low) (hcfs : ReadsCanonical coefficients)
    (hpair : Canonical pair)
    (hloop : weights.s2_grouped_inactive_pair_loop1 iter low coefficients pair=.ok out) : Canonical out := by
  let step := fun s : R × W => weights.s2_grouped_inactive_pair_loop1.body low coefficients s.1 s.2
  let inv := fun s : R × W => Canonical s.2
  let measure := fun s : R × W => s.1.end.val-s.1.start.val
  have hd : ∀ s result, inv s → step s=.ok (.done result) → Canonical result := by
    rintro ⟨r,c⟩ result hc hb
    have he := outer_body_done_same low coefficients r c result hb
    exact he.symm ▸ hc
  have hc : ∀ s s', inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hc hb
    obtain ⟨group,weight,coefficient,product,hn,hw,hcf,hm,ha⟩ :=
      outer_body_cont_source low coefficients r r' c c' hb
    have hwc := AspisR1S9S2WeightCanonicalV1.weight_loop_success_canonical low group _ _ weight hlow
      AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical hw
    have hpc := (AspisR1S9NativeWideDecodedArithmeticV1.actual_mul_success_decoded
      coefficient weight product (hcfs group coefficient hcf) hwc hm).1
    exact (AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded c product c' hc hpc ha).1
  have hm : ∀ s s', step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hb
    obtain ⟨group,weight,coefficient,product,hn,hw,hcf,hm,ha⟩ :=
      outer_body_cont_source low coefficients r r' c c' hb
    obtain ⟨hlt,hgroup,hstart,hend⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r' group hn
    simp only [measure,hstart,hend]
    omega
  have hinit : inv (iter,pair) := hpair
  have hl : Aeneas.Std.loop step (iter,pair)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure inv Canonical hd hc hm _ out hinit hl

variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Complete optimized S2 helper canonicality: all byte/initial coefficient,
masked-weight and output-carry guards are internally discharged. Only the
actual low input's canonicality and SAME accepted helper call remain. -/
theorem s2_helper_success_canonical (f : Slice U8) (low : Low) (out : W)
    (hlow : ReadsCanonical low)
    (h : weights.s2_grouped_inactive_pair f low=.ok out) : Canonical out := by
  unfold weights.s2_grouped_inactive_pair at h
  obtain ⟨coefficients,hcoeff,houter⟩ := bind_success _ _ _ h
  have hc := AspisR1S9S2CoefficientsCanonicalV1.zero_seed_coefficient_success_canonical f coefficients hcoeff
  exact outer_loop_success_canonical low coefficients _ _ out hlow hc
    AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical houter

/-- The public dispatch also needs its actual exact-span condition. Pair's
floor(length/32)=64 does NOT imply this; generic fallback remains separate. -/
theorem s2_exact_span_dispatch_success_canonical (self : weights.Weights) (f : Slice U8)
    (low : Low) (out : W) (hs2 : self.variant=transport.Variant.S2)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (hlow : ReadsCanonical low)
    (h : weights.grouped_inactive_pair self f low=.ok out) : Canonical out := by
  have hvariant : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant transport.Variant.S2=.ok true := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  unfold weights.grouped_inactive_pair at h
  rw [hvariant] at h
  simp only [bind_tc_ok,lift,hspan,↓reduceIte] at h
  exact s2_helper_success_canonical f low out hlow h

#print axioms outer_body_cont_source
#print axioms outer_body_done_same
#print axioms outer_loop_success_canonical
#print axioms s2_helper_success_canonical
#print axioms s2_exact_span_dispatch_success_canonical
end AspisR1S9S2InactiveCanonicalV1
