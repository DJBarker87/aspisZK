import NIL_ResumeTailCut
set_option autoImplicit false
noncomputable section
namespace NIL_ResumeSplit
open Aeneas Aeneas.Std Result NIL_Carriers AspisR1

def tail (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : Fresh.V) (end1 : Usize) (next : U8) :=
 NIL_ResumeTailCut.tail NIL_FreshOps.mapError
 (fun x=>ok x) (ok (unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
 (NIL_FreshOps.filled reserved) NIL_FreshOps.semantic NIL_FreshOps.weights NIL_FreshOps.validate
 NIL_FreshOps.readK NIL_FreshOps.readE NIL_FreshOps.raw
 (fun v=>CheckpointBytes4Ops.finalLen (variant v)) (NIL_FreshOps.digest d) bytes v end1 next

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (v : Fresh.V) (hash : H) :
 NIL_FreshOps.resume reserved d bytes proof public1 v hash=
 NIL_ResumePrefixCut.fresh (NIL_FreshOps.digest d) bytes proof public1 v hash
 (tail reserved d bytes v) := by rfl
#print axioms source
end NIL_ResumeSplit
