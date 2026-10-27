import Port4B_CountInstall
import Port4B_Padding

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_SlotInstall
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical MultiproofConeSlices OraclePortSelectedDraft

/-- The seven boundary offsets of the six admitted fixed physical slots. -/
theorem offset_bound (n : Nat) (bound : n≤6) : slotStart n≤57607 := by
  interval_cases n <;> decide

def offset (n : Nat) (bound : n≤6) : Usize := UScalar.ofNat (slotStart n) (by
  have small := offset_bound n bound
  scalar_tac)

theorem offset_step (n : Nat) : slotStart (n+1)=slotStart n+32*capacity n := by
  simp only [slotStart,List.range_succ,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
  omega

/-- P6 pure slot-offset lowering. The source offset loop is the sum of the
preceding capacities; every admitted offset fits without release wrapping. -/
def nodeSlot (proof : Slice U8) (slot : Usize) : Result (Slice U8) :=
  if small : slot.val<6 then
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=offset slot.val (by omega),«end»:=offset (slot.val+1) (by omega)}
  else fail .arrayOutOfBounds

def install (base : Port3_NativeBatchBody.Ops) : Port3_NativeBatchBody.Ops :=
  {Port4B_CountInstall.install base with op3:=nodeSlot}

theorem physical (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (b k : Nat) (hb : b<2) (hk : k<3) (slot : Usize) (value : slot.val=3*b+k) :
    ∃ view, nodeSlot proof slot=ok view ∧ view.val.length=32*capacity (3*b+k) ∧
      bytesOf view.val=OraclePortCompactDraft.slice parsed.wire (slotStart (3*b+k)) (32*capacity (3*b+k)) := by
  have small : slot.val<6 := by omega
  obtain ⟨start,finish,view,hs,he,read,size,bytes⟩ :=
    MultiproofConeSlotAdapters.slot_view proof len parsed wire b k hb hk
  have startEq : offset slot.val (by omega)=start := by
    apply UScalar.eq_of_val_eq
    change slotStart slot.val=start.val
    rw [value,hs]
  have finishEq : offset (slot.val+1) (by omega)=finish := by
    apply UScalar.eq_of_val_eq
    change slotStart (slot.val+1)=finish.val
    rw [offset_step,value,he,hs]
  refine ⟨view,?_,size,bytes⟩
  simp only [nodeSlot,dif_pos small,startEq,finishEq,read]

/-- Required14 supplies the very SAME native slot buffer, via byte-carrier
injectivity. No extra native node-view or successful read is a premise. -/
theorem caller {Observer X : Type} (c : S2LeadInterface.Inputs Observer)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (stored pub saved : AspisV8R19.DuplexFrames.Bytes) (parsed : OraclePortCompactDraft.Parsed)
    (facts : S2LeadInterface.S2CallerFacts c D hash H stored pub saved parsed)
    (proof : Slice U8) (len : proof.val.length=57607) (wire : parsed.wire=bytesOf proof.val)
    (b k : Nat) (hb : b<2) (hk : k<3) (slot : Usize) (value : slot.val=3*b+k) :
    nodeSlot proof slot=ok (c.nodes b k) := by
  obtain ⟨view,read,size,bytes⟩ := physical proof len parsed wire b k hb hk slot value
  have same : view=c.nodes b k := Subtype.ext
    (MultiproofConeByteEquality.bytes_injective (bytes.trans (facts.nodeViews b k hb hk).symm))
  exact read.trans (congrArg Result.ok same)

#print axioms offset_bound
#print axioms offset_step
#print axioms physical
#print axioms caller
end AspisR1.Port4B_SlotInstall
end
