import NGC_HeapRef.Funs
import NGC_FinishRef.Funs
import OraclePortStdAllocation
import CheckpointBytes3Namespaces
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_ReferenceValues
open Aeneas Aeneas.Std Result
/-- Effect-free Clone is explicit, rather than inferred for arbitrary Copy. -/
theorem resize_empty {T : Type} (clone : core.clone.Clone T) (n : Usize) (value : T)
 (pureClone : clone.clone value=ok value) :
 ∃ out : alloc.vec.Vec T, alloc.vec.Vec.resize clone (alloc.vec.Vec.new T) n value=ok out ∧
 out.val=List.replicate n.val value := by
 obtain ⟨out,run,cells⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.resize_spec clone (alloc.vec.Vec.new T) n value pureClone)
 refine ⟨out,run,?_⟩
 simpa [alloc.vec.Vec.new, List.resize] using cells

def fromRef (q : NGC_HeapRef.Q) : AspisR1Stage2.aspis_core.field.QM31 :=
 ⟨⟨q.limbs.val[0]'(by simp [q.limbs.property]),q.limbs.val[1]'(by simp [q.limbs.property])⟩,
  ⟨q.limbs.val[2]'(by simp [q.limbs.property]),q.limbs.val[3]'(by simp [q.limbs.property])⟩⟩
def toRef (q : AspisR1Stage2.aspis_core.field.QM31) : NGC_HeapRef.Q :=
 ⟨Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]⟩
theorem roundtrip (q : AspisR1Stage2.aspis_core.field.QM31) : fromRef (toRef q)=q := by
 cases q with | mk a b=>cases a;cases b;rfl

def mapResult (r : core.result.Result (alloc.vec.Vec NGC_HeapRef.Q) Unit) :
 Except OraclePortStdAllocation.AllocationError (alloc.vec.Vec AspisR1Stage2.aspis_core.field.QM31) :=
 match r with
 | .Ok out=>.ok (CheckpointBytes3Namespaces.mapVec fromRef out)
 | .Err _=>.error .allocation
/-- NCO-pinned extracted safe reference equals the adopted full heap value
model for BOTH reservation outcomes; no successful-result premise is assumed. -/
theorem heap (n : Usize) (q : NGC_HeapRef.Q) (reserved : Bool) :
 (do let out←NGC_HeapRef.filled_ref n q reserved;ok (mapResult out))=
 OraclePortStdAllocation.filled n (fromRef q) reserved := by
 cases reserved with
 | false=>rfl
 | true=>
  obtain ⟨out,run,cells⟩ := resize_empty NGC_HeapRef.Q.Insts.CoreCloneClone n q rfl
  rw [OraclePortStdAllocation.filled_exact]
  simp [NGC_HeapRef.filled_ref,run,mapResult,OraclePortStdAllocation.filledSpec,
   CheckpointBytes3Namespaces.mapVec,cells,List.map_replicate]
/-- The extracted one-window assignment has complete update/frame semantics. -/
theorem finish_step (weights : Slice NGC_FinishRef.Q) (index : Usize)
 (value : NGC_FinishRef.Q) (inside : index.val<weights.val.length) :
 ∃ out,NGC_FinishRef.finish_step_ref weights index value=ok out ∧ out=weights.set index value := by
 exact WP.spec_imp_exists (Slice.update_spec weights index value inside)
#print axioms resize_empty
#print axioms roundtrip
#print axioms heap
#print axioms finish_step
end AspisR1.NGC_ReferenceValues
end
