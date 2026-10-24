import S9RegularCell4FrameV1
import S9SharedHighFrameV1
import S9ActiveFourValueStepV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActiveIncomingZeroV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1 (W Powers Parts Scratch)
open AspisR1S9ActiveFourValueStepV1 (cell4)
open AspisR1S9FactorArrayEntryV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

theorem cell4_read (parts : Parts) : Array.index_usize parts 4#usize=.ok (cell4 parts) :=
  index_atN parts 4#usize (by decide)

theorem zero_seed_cell4 : cell4 (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO)=
    aspis_core.field.wide_exact.WideExact.ZERO := by
  unfold cell4 atN
  change (List.replicate 7 aspis_core.field.wide_exact.WideExact.ZERO)[4]'_=
    aspis_core.field.wide_exact.WideExact.ZERO
  rw [List.getElem_replicate]

theorem inactive_write_preserves_cell4 (initial middle : Parts) (inactive : W)
    (h : Array.update initial 0#usize inactive=.ok middle) : cell4 middle=cell4 initial := by
  have he := accepted_update_eq_set initial 0#usize (by decide) inactive middle h
  subst middle
  unfold cell4
  rw [atN_set initial 0#usize 4#usize inactive (by decide) (by decide)] <;> rfl

/-- Actual regular source kinds never write4, so its real initialized zero
survives without arithmetic, canonicality or another part's value premise. -/
theorem regular_cell4_zero (self : weights.Weights) (shared : Bool) (alpha : Slice W)
    (f : Slice U8) (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch)
    (partsRegular : Parts) (hs2 : self.variant=transport.Variant.S2)
    (hregular : weights.process_regular_kinds self shared alpha f 2#usize n ap0 ap1 scratch
      (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO)=
      .ok (.Ok (),scratchOut,partsRegular)) : cell4 partsRegular=aspis_core.field.wide_exact.WideExact.ZERO := by
  have hf := AspisR1S9RegularCell4FrameV1.actual_regular_success_cell4_frame
    self shared alpha f n ap0 ap1 scratch scratchOut
    (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO) partsRegular hs2 hregular
  change cell4 partsRegular=cell4 (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO) at hf
  exact hf.trans zero_seed_cell4

theorem shared_high_preserves_cell4 (partials : Array W 4#usize) (self : weights.Weights)
    (ap0 ap1 : Powers) (initial final : Parts)
    (h : weights.shared_high partials self ap0 ap1 initial=.ok (.Ok (),final)) :
    cell4 final=cell4 initial :=
  AspisR1S9SharedHighFrameV1.shared_high_success_frame partials self ap0 ap1 initial final h
    4#usize (by decide) (by decide) (by decide)

#print axioms cell4_read
#print axioms zero_seed_cell4
#print axioms inactive_write_preserves_cell4
#print axioms regular_cell4_zero
#print axioms shared_high_preserves_cell4
end AspisR1S9ActiveIncomingZeroV1
