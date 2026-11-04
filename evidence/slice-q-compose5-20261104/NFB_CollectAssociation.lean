import NFB_CollectorTrace
import NFB_TerminalCuts
set_option autoImplicit false
noncomputable section
namespace NFB_CollectAssociation
open Aeneas Aeneas.Std Result AspisR1
open NFB_CollectorTrace
open NEW_GeometryDictionary

/-- The adopted collector and the native guard-local store induction have
ONE exact initialized payload and publication length. No child result premise. -/
theorem complete (flat : alloc.vec.Vec U32) (count : Usize)
 (bound : count.val≤22) (size : flat.val.length=5*count.val) :
 ∃ out : alloc.vec.Vec (Array U32 5#usize),
 Port4C_CollectLoop.collect (Port4C_GeometryInverse.install
  (NEB_ActualGeometryModel.install NEW_GeometryRawInterface.ops NEW_GeometryDictionary.err)) flat count=ok out ∧
 finish (fill ((List.range count.val).map (Port4C_CollectLoop.record flat))
  (⟨[],0⟩ : Guard (Array U32 5#usize)))=⟨out.val,out.val.length⟩ ∧
 out.val.length=count.val := by
 obtain ⟨out,run,contents,length⟩ := Port4C_CollectLoop.total
  (Port4C_GeometryInverse.install
   (NEB_ActualGeometryModel.install NEW_GeometryRawInterface.ops NEW_GeometryDictionary.err))
  flat count bound size
 refine ⟨out,run,?_,length⟩
 rw [NFB_CollectorTrace.complete,←contents]

/-- Five initialized native slots match every lane of the adopted callback. -/
theorem array_complete (flat : alloc.vec.Vec U32) (row : Nat) :
 finish (fill (Port4C_CollectLoop.record flat row).val (⟨[],0⟩ : Guard U32))=
 ⟨(Port4C_CollectLoop.record flat row).val,5⟩ := by
 rw [NFB_CollectorTrace.complete]
 congr 1
#print axioms complete
#print axioms array_complete
end NFB_CollectAssociation
end
