import Port10AUTH_FirstBoth
import Port4B_FoldedCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_Views
open Aeneas Aeneas.Std Result VTop_Stages
open MultiproofConeCanonical MultiproofConeSlices OraclePortSelectedDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- Fixed physical slices, independent of Parsed and of oracle answers. -/
def nodes (proof : Slice U8) (b k : Nat) : Slice U8 :=
  if h : 3*b+k<6 then sub proof
    (Port4B_SlotInstall.offset (3*b+k) (by omega))
    (Port4B_SlotInstall.offset (3*b+k+1) (by omega))
  else proof

/-- The actual installed nodeSlot returns this view; no caller nodeViews field. -/
theorem node_call (proof : Slice U8) (len : proof.val.length=57607)
    (b k : Nat) (hb : b<2) (hk : k<3) :
    Port4B_SlotInstall.nodeSlot proof (Usize.ofNat (3*b+k) (by scalar_tac))=ok (nodes proof b k) := by
  have small : 3*b+k<6 := by omega
  unfold Port4B_SlotInstall.nodeSlot nodes
  simp only [UScalar.ofNat_val,dif_pos small]
  apply range_total
  · change slotStart (3*b+k)≤slotStart (3*b+k+1)
    rw [Port4B_SlotInstall.offset_step]
    omega
  · change slotStart (3*b+k+1)≤proof.val.length
    rw [len]
    exact Port4B_SlotInstall.offset_bound _ (by omega)

theorem node_bytes (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val) :
    ∀ b k, b<2 → k<3 → bytesOf (nodes proof b k).val=
      OraclePortCompactDraft.slice parsed.wire (slotStart (3*b+k)) (32*capacity (3*b+k)) := by
  intro b k hb hk
  obtain ⟨view,called,size,bytes⟩ := Port4B_SlotInstall.physical proof len parsed wire b k hb hk
    (Usize.ofNat (3*b+k) (by scalar_tac)) rfl
  have same := Result.ok.inj (called.symm.trans (node_call proof len b k hb hk))
  exact same ▸ bytes

/-- The exact source range/conversion/Std unwrap return determines root2. -/
theorem folded (ops : Ops) (std : Port1_Library.TrustedStd ops)
    (proof view : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (conversion : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)
    (root : Array U8 32#usize)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok conversion)
    (unwrapped : ops.unwrap32 conversion=ok root) :
    root=encodeState (OraclePortBatchDraft.committedRoot parsed 2) := by
  rw [std.result_unwrap32] at unwrapped
  cases conversion with
  | Err e => cases unwrapped
  | Ok r =>
    have same : r=root := Result.ok.inj unwrapped
    subst r
    have bytes := Port4B_FoldedCut.model proof view root len parsed wire range copy
    apply MultiproofConePhysicalTransport.digest_injective
    simpa only [MultiproofConePhysicalTransport.digest_bytes] using bytes

#print axioms node_call
#print axioms node_bytes
#print axioms folded
end AspisR1.Port11PROV_Views
end
