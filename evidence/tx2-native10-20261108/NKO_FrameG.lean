import NKO_ReadonlyFrame
set_option autoImplicit false
noncomputable section
namespace NKO_FrameG
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
/-- Proof argument decoded from the native frame G. The post-view is a
DEFINITION from the checked log-only write footprint, never an endpoint seed. -/
def proof (written heap : Nat → U8) (logBase logSize proofBase : Nat)
 (before : Slice U8) : Slice U8 :=
 ⟨NKO_ReadonlyFrame.view (KMX_CopyMeaning.loop written heap logBase logSize)
   proofBase before.val.length,
  by simpa only [NKO_ReadonlyFrame.view,List.length_map,List.length_range] using before.property⟩

/-- Native pre-state interpretation and disjoint live borrows suffice. No
independently chosen post-view, child output, success or native-log equality. -/
theorem proof_source (written heap : Nat → U8) (logBase logSize proofBase : Nat)
 (before : Slice U8)
 (inputView : before.val=NKO_ReadonlyFrame.view heap proofBase before.val.length)
 (disjoint : proofBase+before.val.length≤logBase ∨ logBase+logSize≤proofBase) :
 proof written heap logBase logSize proofBase before=before := by
 apply Subtype.ext
 change NKO_ReadonlyFrame.view (KMX_CopyMeaning.loop written heap logBase logSize)
  proofBase before.val.length=before.val
 rw [NKO_ReadonlyFrame.view_frame written heap logBase logSize proofBase before.val.length disjoint]
 exact inputView.symm

/-- Complete source input carrier from all independently checked C07 windows.
Only its proof component uses the log-only contract frame. -/
def args (written heap : Nat → U8) (logBase logSize proofBase : Nat)
 (before observed : NKE_QueryInput.Args) : NKE_QueryInput.Args :=
 {observed with proof:=proof written heap logBase logSize proofBase before.proof}

theorem args_source (written heap : Nat → U8) (logBase logSize proofBase : Nat)
 (before observed : NKE_QueryInput.Args)
 (inputView : before.proof.val=NKO_ReadonlyFrame.view heap proofBase before.proof.val.length)
 (disjoint : proofBase+before.proof.val.length≤logBase ∨ logBase+logSize≤proofBase)
 (proofSize : before.proof.val.length=57607)
 (weightSize : before.accumulator.weights.val.length=64)
 (inverseSize : before.geometry.inverses.val.length=12)
 (lineSize : before.geometry.line_z.val.length=12)
 (rawSize : before.pending.raw.val.length=64)
 (prepared : NJJ_Constructors.PreparedCut before.prepared observed.prepared)
 (accumulator : NJJ_Constructors.AccumulatorCut before.accumulator observed.accumulator)
 (powers : ∀ i : Fin 29,observed.powers.val[i.val]?=before.powers.val[i.val]?)
 (geometry : NKE_GeometryCuts.Cut before.geometry observed.geometry)
 (rawWidth : observed.pending.raw.val.length=64)
 (rawCells : ∀ i,i<64 → observed.pending.raw.val[i]?=before.pending.raw.val[i]?)
 (terms : observed.pending.terms=before.pending.terms) :
 args written heap logBase logSize proofBase before observed=before := by
 have same := proof_source written heap logBase logSize proofBase before.proof inputView disjoint
 apply NKE_QueryInput.same _ _ proofSize weightSize inverseSize lineSize rawSize
 refine ⟨?_,?_,prepared,accumulator,powers,geometry,rawWidth,rawCells,terms⟩
 · change (proof written heap logBase logSize proofBase before.proof).val.length=57607
   rw [same,proofSize]
 · intro i _
   change (proof written heap logBase logSize proofBase before.proof).val[i]?=before.proof.val[i]?
   rw [same]
#print axioms proof_source
#print axioms args_source
end NKO_FrameG
