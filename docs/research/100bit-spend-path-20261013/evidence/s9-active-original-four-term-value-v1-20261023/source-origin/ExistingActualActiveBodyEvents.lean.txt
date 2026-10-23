import S9NativeArrayCanonicalV1
import S9NativeFieldActualCanonicalV1
import S9NativeWideDecodedArithmeticV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActiveFourCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeArrayCanonicalV1
abbrev R := core.ops.range.Range Usize
abbrev Parts := Array W 7#usize
abbrev Libra := Array W 4#usize
private theorem bind_success {X Y : Type} (m : Result X) (next : X → Result Y) (out : Y)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem body_cont_source (f : Slice U8) (libra : Libra) (iter iterOut : R) (parts out : Parts)
    (h : weights.Weights.pair_loop8.body f libra iter parts=.ok (.cont (iterOut,out))) :
    ∃ (j : Usize) (carry value coefficient product total : W),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some j,iterOut) ∧
      Array.index_usize parts 4#usize=.ok carry ∧ weights.field f j=.ok value ∧
      Array.index_usize libra j=.ok coefficient ∧
      aspis_core.field.wide_exact.WideExact.mul value coefficient=.ok product ∧
      aspis_core.field.wide_exact.WideExact.add carry product=.ok total ∧
      Array.update parts 4#usize total=.ok out := by
  unfold weights.Weights.pair_loop8.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some j =>
    obtain ⟨carry,hcarry,h⟩ := bind_success _ _ _ h
    obtain ⟨value,hfield,h⟩ := bind_success _ _ _ h
    obtain ⟨coefficient,hcf,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨total,ha,h⟩ := bind_success _ _ _ h
    obtain ⟨updated,hu,h⟩ := bind_success _ _ _ h
    have he := ControlFlow.cont.inj (Result.ok.inj h)
    cases he
    exact ⟨j,carry,value,coefficient,product,total,hn,hcarry,hfield,hcf,hm,ha,hu⟩

theorem body_done_same (f : Slice U8) (libra : Libra) (iter : R) (parts out : Parts)
    (h : weights.Weights.pair_loop8.body f libra iter parts=.ok (.done out)) : out=parts := by
  unfold weights.Weights.pair_loop8.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none => exact (ControlFlow.done.inj (Result.ok.inj h)).symm
  | some j =>
    obtain ⟨carry,hcarry,h⟩ := bind_success _ _ _ h
    obtain ⟨value,hfield,h⟩ := bind_success _ _ _ h
    obtain ⟨coefficient,hcf,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨total,ha,h⟩ := bind_success _ _ _ h
    obtain ⟨updated,hu,h⟩ := bind_success _ _ _ h
    cases h

/-- Both two-fold branches use the same four active coefficient updates. -/
theorem unshared_active_eq (iter : R) (f : Slice U8) (parts : Parts) (libra : Libra) :
    weights.Weights.pair_loop16 iter f parts libra=weights.Weights.pair_loop8 iter f parts libra := by rfl

variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- All canonicality of actual input bytes and child arithmetic is derived
from this SAME accepted source loop. Only incoming parts and actual private
weights canonicality remain explicit, with no raw-dot product law needed. -/
theorem active_loop_success_canonical (f : Slice U8) (libra : Libra) (iter : R) (parts out : Parts)
    (hp : ReadsCanonical parts) (hl : ReadsCanonical libra)
    (hloop : weights.Weights.pair_loop8 iter f parts libra=.ok out) : ReadsCanonical out := by
  let step := fun s : R × Parts => weights.Weights.pair_loop8.body f libra s.1 s.2
  let inv := fun s : R × Parts => ReadsCanonical s.2
  let measure := fun s : R × Parts => s.1.end.val-s.1.start.val
  have hd : ∀ s result, inv s → step s=.ok (.done result) → ReadsCanonical result := by
    rintro ⟨r,c⟩ result hc hb
    have he := body_done_same f libra r c result hb
    exact he.symm ▸ hc
  have hc : ∀ s s', inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hcan hb
    obtain ⟨j,carry,value,coefficient,product,total,hn,hcarry,hfield,hcf,hm,ha,hu⟩ :=
      body_cont_source f libra r r' c c' hb
    have hv := AspisR1S9NativeFieldActualCanonicalV1.field_success_native_canonical f j value hfield
    have hprod := (AspisR1S9NativeWideDecodedArithmeticV1.actual_mul_success_decoded
      value coefficient product hv (hl j coefficient hcf) hm).1
    have htotal := (AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded
      carry product total (hcan 4#usize carry hcarry) hprod ha).1
    exact accepted_update_preserves_canonical c c' 4#usize total (by decide) hcan htotal hu
  have hm : ∀ s s', step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,c⟩ ⟨r',c'⟩ hb
    obtain ⟨j,carry,value,coefficient,product,total,hn,hcarry,hfield,hcf,hm,ha,hu⟩ :=
      body_cont_source f libra r r' c c' hb
    obtain ⟨hlt,hj,hstart,hend⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r' j hn
    simp only [measure,hstart,hend]
    omega
  have hinit : inv (iter,parts) := hp
  have hs : Aeneas.Std.loop step (iter,parts)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure inv ReadsCanonical hd hc hm _ out hinit hs

theorem unshared_active_success_canonical (f : Slice U8) (libra : Libra) (iter : R) (parts out : Parts)
    (hp : ReadsCanonical parts) (hl : ReadsCanonical libra)
    (hloop : weights.Weights.pair_loop16 iter f parts libra=.ok out) : ReadsCanonical out := by
  rw [unshared_active_eq] at hloop
  exact active_loop_success_canonical f libra iter parts out hp hl hloop

#print axioms body_cont_source
#print axioms body_done_same
#print axioms unshared_active_eq
#print axioms active_loop_success_canonical
#print axioms unshared_active_success_canonical
end AspisR1S9ActiveFourCanonicalV1
