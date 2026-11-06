import NLI_SourceEquality
import NLC_CopyFrames
set_option autoImplicit false
namespace AspisR1.NLI_ViewFrames
open Aeneas Aeneas.Std
abbrev Memory := Nat → U8
structure View where
 start : Nat
 length : Nat
/-- A value realization is supplied by the original admitted input/parser.
An address comparison alone is deliberately insufficient. -/
def Realizes (memory : Memory) (view : View) (value : Fin view.length → U8) : Prop :=
 ∀ i, memory (view.start+i.val)=value i
/-- Descriptor preservation and a pointwise read-only frame transport the
ORIGINAL value realization to the child view. No payload is inferred from
an integer address, and no independently chosen child bytes are assumed. -/
theorem realized_frame (before after : Memory) (view : View)
 (value : Fin view.length → U8) (original : Realizes before view value)
 (frame : ∀ i : Fin view.length,after (view.start+i.val)=before (view.start+i.val)) :
 Realizes after view value := by
 intro i
 exact (frame i).trans (original i)
theorem family_frame (before after : Memory) (views : Fin 27 → View)
 (values : ∀ row, Fin (views row).length → U8)
 (original : ∀ row,Realizes before (views row) (values row))
 (frame : ∀ address,after address=before address) :
 ∀ row,Realizes after (views row) (values row) := by
 intro row
 exact realized_frame before after (views row) (values row) (original row) (fun i=>frame _)
theorem bounded_family_frame (before after : Memory) (capacity : Nat)
 (views : Fin 27 → View) (values : ∀ row, Fin (views row).length → U8)
 (bounded : ∀ row,(views row).start+(views row).length≤capacity)
 (original : ∀ row,Realizes before (views row) (values row))
 (frame : ∀ address,address<capacity → after address=before address) :
 ∀ row,Realizes after (views row) (values row) := by
 intro row
 apply realized_frame before after (views row) (values row) (original row)
 intro i
 apply frame
 have hi:=i.isLt
 have hb:=bounded row
 omega
#print axioms bounded_family_frame
/-- An exact KMX copy's disjointness frame supplies the same value law for a
read-only view. This uses the pinned KMX theorem, not an unfolded byte loop. -/
theorem disjoint_copy_frame (src before : Memory) (start count : Nat) (view : View)
 (value : Fin view.length → U8) (original : Realizes before view value)
 (disjoint : view.start+view.length≤start ∨ start+count≤view.start) :
 Realizes (KMX_CopyMeaning.loop src before start count) view value := by
 apply realized_frame before _ view value original
 intro i
 apply NLC_CopyFrames.retained_window
 have bound:=i.isLt
 omega
#print axioms realized_frame
#print axioms family_frame
#print axioms disjoint_copy_frame
end AspisR1.NLI_ViewFrames
