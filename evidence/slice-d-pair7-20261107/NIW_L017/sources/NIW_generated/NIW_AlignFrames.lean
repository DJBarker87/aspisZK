import NIW_AlignBoundary
import NIT_ArrayFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFrames
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl NIW_AlignBoundary Classical

/-- Selector-independent native state snapshots. Windows project them; the
parent body and its replies do not depend on the observation selectors. -/
structure Stream where
 base : Log
 partialCommonCells : CommonCells
 highBeforeParts : Parts
 highPartialValues : Powers

def window (l : Stream) (i slot power : Nat) : Log :=
 {l.base with
  partialCommon := kpick l.partialCommonCells i
  highBefore := epick l.highBeforeParts slot
  highPartial := epick l.highPartialValues power}

def cutStream (shared : Bool) (partsAddress : Nat) (l : Stream)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit) : Prop :=
 ∀ i,i<16 → ∀ slot,slot<7 → ∀ power,power<4 →
 cut shared partsAddress i slot power (window l i slot power) afterScratch afterParts out

/-- Full mutable Parts post follows from native arbitrary-index windows; error
returns retain the writes of the entered child. No output-success premise. -/
theorem parts_post (shared : Bool) (address : Nat) (l : Stream)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cutStream shared address l afterScratch afterParts out) :
 afterParts=(if enteredHigh shared l.base then l.base.highPartsReply else l.base.partsReply) := by
 apply NIT_ArrayFrames.ext NHI_Scalar.zero
 intro k hk
 change epick afterParts k=epick _ k
 rcases native 0 (by decide) k hk 0 (by decide) with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,frame,_⟩
 exact frame

theorem common_to_partial (shared : Bool) (address : Nat) (l : Stream)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cutStream shared address l afterScratch afterParts out)
 (entered : enteredPartial shared l.base) : l.partialCommonCells=l.base.commonReply := by
 apply NIT_ArrayFrames.ext FIo_Native.aspis_core.field.QM31.ZERO
 intro k hk
 change kpick l.partialCommonCells k=kpick l.base.commonReply k
 rcases native k hk 0 (by decide) 0 (by decide) with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,frame,_⟩
 exact frame entered

/-- Regular's actual mutable post is high's full pre-state. -/
theorem regular_to_high (shared : Bool) (address : Nat) (l : Stream)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cutStream shared address l afterScratch afterParts out)
 (entered : enteredHigh shared l.base) : l.highBeforeParts=l.base.partsReply := by
 apply NIT_ArrayFrames.ext NHI_Scalar.zero
 intro k hk
 change epick l.highBeforeParts k=epick l.base.partsReply k
 exact (NIW_AlignBoundary.regular_to_high shared address 0 k 0 (window l 0 k 0)
  afterScratch afterParts out (native 0 (by decide) k hk 0 (by decide)) entered).2

theorem partial_to_high (shared : Bool) (address : Nat) (l : Stream)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cutStream shared address l afterScratch afterParts out)
 (entered : enteredHigh shared l.base) (values : Powers) (returned : l.base.partialReply=.Ok values) :
 l.highPartialValues=values := by
 apply NIT_ArrayFrames.ext NHI_Scalar.zero
 intro k hk
 change epick l.highPartialValues k=epick values k
 exact NIW_AlignBoundary.partial_to_high shared address 0 0 k (window l 0 0 k)
  afterScratch afterParts out (native 0 (by decide) 0 (by decide) k hk) entered values returned

#print axioms parts_post
#print axioms common_to_partial
#print axioms regular_to_high
#print axioms partial_to_high
end AspisR1.NIW_AlignFrames
