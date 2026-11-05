import NIS_SdkWriteLoop
import S2W_WrapperLaws
set_option autoImplicit false
namespace NIJ_SdkCopyCanonical
open AspisR1.S2Trust AspisR1.S2W_TrustedStd

theorem unchanged {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8)
 (start n : Nat) :
 NIJ_SdkWriteLoop.copy s g source start n=
 {s with payload:=(NIJ_SdkWriteLoop.copy s g source start n).payload} := by
 induction n with
 | zero => rfl
 | succ n ih =>
   simp only [NIJ_SdkWriteLoop.copy,writeAt]
   rw [ih]

theorem payload {F : Type} (s : Heap F) (g : Guard) (src : Payload) :
 (NIJ_SdkWriteLoop.copy s g src.contents 0 (s.payload g.cell).descriptor.length).payload=
 (copyHeap s g.cell src).payload := by
 funext cell
 by_cases same : cell=g.cell
 · subst cell
   have description:=NIJ_SdkWriteLoop.descriptor s g src.contents 0 (s.payload g.cell).descriptor.length g.cell
   have complete:=cells_compose (s.payload g.cell) src
     ((NIJ_SdkWriteLoop.copy s g src.contents 0 (s.payload g.cell).descriptor.length).payload g.cell)
     description (by
       intro i
       by_cases inside : i<(s.payload g.cell).descriptor.length
       · simp only [inside,ite_true]
         exact NIJ_SdkWriteLoop.contents s g src.contents 0 _ i (by omega)
       · simp only [inside,ite_false]
         exact NIJ_SdkWriteLoop.outside s g src.contents 0 _ i (by omega))
   simpa only [copyHeap,put,ite_true] using complete
 · rw [NIJ_SdkWriteLoop.other_cell _ _ _ _ _ _ same]
   simp only [copyHeap,put,same,ite_false]

/-- Exact equality with the canonical SInt2 bulk-copy heap. No new reference
model, independent output observation or saved-byte equation is assumed. -/
theorem source {F : Type} (s : Heap F) (g : Guard) (src : Payload) :
 NIJ_SdkWriteLoop.copy s g src.contents 0 (s.payload g.cell).descriptor.length=
 copyHeap s g.cell src := by
 rw [unchanged]
 exact congrArg (fun p => {s with payload:=p}) (payload s g src)

#print axioms unchanged
#print axioms payload
#print axioms source
end NIJ_SdkCopyCanonical
