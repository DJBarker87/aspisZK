import S9NativeArrayCanonicalV1
import S9NativeFieldActualCanonicalV1
import S9NativeWideDecodedArithmeticV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9S2CoefficientsCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeArrayCanonicalV1
abbrev R := core.ops.range.Range Usize
abbrev Coefficients := Array W 12#usize
private theorem bind_success {X Y : Type} (m : Result X) (next : X → Result Y) (out : Y)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Exact actual grouped-coefficient continuation witnesses. No static64table
is unfolded and no desired byte/read/canonicality conclusion is assumed. -/
theorem body_cont_source (f : Slice U8) (iter iterOut : R) (a out : Coefficients)
    (h : weights.s2_grouped_inactive_pair_loop0.body f iter a=.ok (.cont (iterOut,out))) :
    ∃ (j : Usize) (code : U8) (group : Usize) (old value total : W),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some j,iterOut) ∧
      Array.index_usize weights.S2_INACTIVE_GROUPS j=.ok code ∧
      group=UScalar.cast .Usize code ∧ Array.index_usize a group=.ok old ∧
      weights.field f j=.ok value ∧
      aspis_core.field.wide_exact.WideExact.add old value=.ok total ∧
      Array.update a group total=.ok out := by
  unfold weights.s2_grouped_inactive_pair_loop0.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some j =>
    obtain ⟨code,hcode,h⟩ := bind_success _ _ _ h
    obtain ⟨group,hgroup,h⟩ := bind_success _ _ _ h
    obtain ⟨old,hold,h⟩ := bind_success _ _ _ h
    obtain ⟨value,hfield,h⟩ := bind_success _ _ _ h
    obtain ⟨total,hadd,h⟩ := bind_success _ _ _ h
    obtain ⟨updated,hupdate,h⟩ := bind_success _ _ _ h
    have he := ControlFlow.cont.inj (Result.ok.inj h)
    cases he
    exact ⟨j,code,group,old,value,total,hn,hcode,(Result.ok.inj hgroup).symm,hold,hfield,hadd,hupdate⟩

theorem body_done_same (f : Slice U8) (iter : R) (a out : Coefficients)
    (h : weights.s2_grouped_inactive_pair_loop0.body f iter a=.ok (.done out)) : out=a := by
  unfold weights.s2_grouped_inactive_pair_loop0.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => exact (ControlFlow.done.inj (Result.ok.inj h)).symm
  | some j =>
    obtain ⟨code,hcode,h⟩ := bind_success _ _ _ h
    obtain ⟨group,hgroup,h⟩ := bind_success _ _ _ h
    obtain ⟨old,hold,h⟩ := bind_success _ _ _ h
    obtain ⟨value,hfield,h⟩ := bind_success _ _ _ h
    obtain ⟨total,hadd,h⟩ := bind_success _ _ _ h
    obtain ⟨updated,hupdate,h⟩ := bind_success _ _ _ h
    cases h

variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Every accepted source coefficient accumulation preserves canonicality.
Actual decoder success provides each input canonicality even for wrapping
field indices. The actual successful coefficient read supplies group bounds. -/
theorem coefficient_loop_success_canonical (f : Slice U8) (iter : R)
    (a out : Coefficients) (ha : ReadsCanonical a)
    (hloop : weights.s2_grouped_inactive_pair_loop0 iter f a=.ok out) : ReadsCanonical out := by
  let step := fun s : R × Coefficients => weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2
  let inv := fun s : R × Coefficients => ReadsCanonical s.2
  let measure := fun s : R × Coefficients => s.1.end.val-s.1.start.val
  have hd : ∀ s result, inv s → step s=.ok (.done result) → ReadsCanonical result := by
    rintro ⟨r,c⟩ result hc hb
    have he := body_done_same f r c result hb
    exact he.symm ▸ hc
  have hc : ∀ s s', inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hcan hb
    obtain ⟨j,code,group,old,value,total,hn,hcode,hgroup,hold,hfield,hadd,hupdate⟩ :=
      body_cont_source f r r' c c' hb
    have ho : Canonical old := hcan group old hold
    have hv : Canonical value := AspisR1S9NativeFieldActualCanonicalV1.field_success_native_canonical f j value hfield
    have ht := (AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded old value total ho hv hadd).1
    have hg := AspisR1S9ConstructorV3Loop2InnerCanonicalV1.index_success_bound c group old hold
    exact accepted_update_preserves_canonical c c' group total hg hcan ht hupdate
  have hm : ∀ s s', step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hb
    obtain ⟨j,code,group,old,value,total,hn,hcode,hgroup,hold,hfield,hadd,hupdate⟩ :=
      body_cont_source f r r' c c' hb
    obtain ⟨hlt,hj,hstart,hend⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r' j hn
    simp only [measure,hstart,hend]
    omega
  have hinit : inv (iter,a) := ha
  have hl : Aeneas.Std.loop step (iter,a)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure inv ReadsCanonical hd hc hm _ out hinit hl

/-- Source zero initialization discharges the canonical input array guard. -/
theorem zero_seed_coefficient_success_canonical (f : Slice U8) (out : Coefficients)
    (hloop : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok out) : ReadsCanonical out := by
  exact coefficient_loop_success_canonical f _ _ out
    (repeat_canonical 12#usize _ AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical) hloop

#print axioms body_cont_source
#print axioms body_done_same
#print axioms coefficient_loop_success_canonical
#print axioms zero_seed_coefficient_success_canonical
end AspisR1S9S2CoefficientsCanonicalV1
