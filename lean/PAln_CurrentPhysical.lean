import PAln_Row30Source
import PAln_FullCut
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_CurrentPhysical
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical OraclePortCompactDraft

theorem sections (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view)) :
    bytesOf (retainedView view).round0.val=slice (bytesOf proof.val) 7527 224 ∧
    bytesOf (retainedView view).round1.val=slice (bytesOf proof.val) 7783 224 ∧
    bytesOf (retainedView view).final_message.val=slice (bytesOf proof.val) 8007 2048 := by
  obtain ⟨selected,call,same⟩ := PAln_ViewCuts.current proof semantic y1 view accepted
  rw [←same]
  exact PAln_Physical.opening_sections proof semantic y1 selected call

theorem second (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view))
    (root : Array U8 32#usize) (bytes1 bytes2 : alloc.vec.Vec U8)
    (unwrapped : core.option.Option.unwrap (retainedView view).folded_root=ok root)
    (first : alloc.vec.Vec.extend_from_slice core.clone.CloneU8
      (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok bytes1)
    (second : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 (retainedView view).round1=ok bytes2) :
    bytesOf bytes2.val=slice (bytesOf proof.val) 7751 256 := by
  obtain ⟨selected,call,same⟩ := PAln_ViewCuts.current proof semantic y1 view accepted
  rw [←same] at unwrapped second
  exact PAln_Row30Source.bytes proof semantic y1 selected call root bytes1 bytes2 unwrapped first second

#print axioms sections
#print axioms second
end AspisR1.PAln_CurrentPhysical
