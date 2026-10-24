import Port10AUTH_Batch
import Port9OR_Installed

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Dictionary
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)

/-- Hash-free padding predicate's dictionary is phantom. Actual digest reads
remain explicit instructions; this does not change primitive failure policy. -/
theorem loop (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D E : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Digest) (kind lo n slot : Usize) (keys : Array U64 16#usize)
    (fuel : Nat) (idx : Indices) (val : Values) (d pos : Usize) :
    Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys fuel idx val d pos=
      Port9OR_BatchLoop.code base E hash proof root kind lo n slot keys fuel idx val d pos := by
  induction fuel generalizing idx val d pos with
  | zero => rfl
  | succ fuel ih =>
    simp only [Port9OR_BatchLoop.code,Port9OR_BatchLoop.body_dictionary base D E]
    apply congrArg (CheckpointBytes5Effect.bind (Port9OR_BatchStep.body base E proof root kind hash lo n slot keys idx val d pos))
    funext out
    cases out with
    | done result => rfl
    | cont next => obtain ⟨ni,nv,nd,np⟩ := next;exact ih ni nv nd np

theorem tree (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D E : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Digest)
    (batch kind : Usize) (idx : Indices) (val : Values) :
    Port9OR_BatchTree.code base D hash proof queries root batch kind idx val=
      Port9OR_BatchTree.code base E hash proof queries root batch kind idx val := by
  simp only [Port9OR_BatchTree.code,loop base D E]

theorem batch (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D E : aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Digest) (which : Usize) :
    Port9OR_Batch.code base D hash proof p folded which=Port9OR_Batch.code base E hash proof p folded which := by
  simp only [Port9OR_Batch.code,Port9OR_Batch.values,tree base D E]

#print axioms loop
#print axioms tree
#print axioms batch
end AspisR1.Port10AUTH_Dictionary
end
