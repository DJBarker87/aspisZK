import F3J_LengthFrame
import PAln_CurrentPhysical
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_OpeningPayloads
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open OraclePortCompactDraft MultiproofConeCanonical

theorem selected (proof semantic y1 : Slice U8) (view : verifier.View)
    (source : sourceView proof semantic y1=ok (.Ok view))
    (p : Parsed) (wire : p.wire=bytesOf proof.val)
    (y1Frame : bytesOf view.y1.val=expand 29 (slice (bytesOf proof.val) 7031 464))
    (root : Array U8 32#usize) (bytes1 bytes2 : alloc.vec.Vec U8)
    (unwrapped : core.option.Option.unwrap (retainedView view).folded_root=ok root)
    (first : alloc.vec.Vec.extend_from_slice core.clone.CloneU8
      (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok bytes1)
    (second : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 (retainedView view).round1=ok bytes2) :
    rowBytes p 27=framed (bytesOf (retainedView view).y1.val) ∧
    rowBytes p 29=framed (bytesOf (retainedView view).round0.val) ∧
    rowBytes p 30=framed (bytesOf bytes2.val) ∧
    rowBytes p 31=framed (bytesOf (retainedView view).final_message.val) ∧
    rowBytes p 32=framed [] := by
  have sections := PAln_CurrentPhysical.sections proof semantic y1 view source
  have joined := PAln_CurrentPhysical.second proof semantic y1 view source root bytes1 bytes2 unwrapped first second
  refine ⟨?_,?_,?_,?_,?_⟩
  · change framed (expand 29 (slice p.wire 7031 464))=_
    rw [wire,← y1Frame]
    rfl
  · change framed (slice p.wire 7527 224)=_
    rw [wire,← sections.1]
  · change framed (slice p.wire 7751 256)=_
    rw [wire,← joined]
  · change framed (slice p.wire 8007 2048)=_
    rw [wire,← sections.2.2]
  · rfl

#print axioms selected
end AspisR1.F3J_OpeningPayloads
end
