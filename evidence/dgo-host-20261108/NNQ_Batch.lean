import NNQ_DSim
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port9OR_BatchStep (Indices Values)

theorem batch_loop_eq {H : Type} (base : Port3_NativeBatchBody.Ops)
    (D1 D2 : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot : Usize)
    (keys : Array U64 16#usize) (fuel : Nat) (idx : Indices) (val : Values) (d pos : Usize) :
    Port9OR_BatchLoop.code base D1 hash proof root tree lo n slot keys fuel idx val d pos =
    Port9OR_BatchLoop.code base D2 hash proof root tree lo n slot keys fuel idx val d pos := by
  induction fuel generalizing idx val d pos with
  | zero => rfl
  | succ fuel ih =>
    simp only [Port9OR_BatchLoop.code, Port9OR_BatchLoop.body_dictionary base D1 D2, ih]

theorem batch_tree_eq {H : Type} (base : Port3_NativeBatchBody.Ops)
    (D1 D2 : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
    (batch tree : Usize) (idx : Indices) (val : Values) :
    Port9OR_BatchTree.code base D1 hash proof queries root batch tree idx val =
    Port9OR_BatchTree.code base D2 hash proof queries root batch tree idx val := by
  simp only [Port9OR_BatchTree.code, batch_loop_eq base D1 D2]

theorem batch_values_eq {H : Type} (base : Port3_NativeBatchBody.Ops)
    (D1 D2 : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array (Array U8 32#usize) 3#usize) (which : Usize) :
    Port9OR_Batch.values base D1 hash proof queries roots which =
    Port9OR_Batch.values base D2 hash proof queries roots which := by
  simp only [Port9OR_Batch.values, batch_tree_eq base D1 D2]

theorem batch_source_eq {H : Type} (D1 D2 : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array (Array U8 32#usize) 2#usize) (folded : Array U8 32#usize) (which : Usize) :
    SdkC_BatchSource.code D1 hash proof queries roots folded which =
    SdkC_BatchSource.code D2 hash proof queries roots folded which := by
  simp only [SdkC_BatchSource.code, batch_values_eq _ D1 D2]

theorem batch_eq {H : Type} (D1 D2 : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (hash : H) (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) :
    GExq_BatchSource.current D1 hash proof p root = GExq_BatchSource.current D2 hash proof p root := by
  unfold GExq_BatchSource.current
  rw [batch_source_eq _ (⟨D2.coremarkerCopyInst,D2.digest⟩ : aspis_core.digest.Digest32 H)]

theorem batch_stage_eq {H : Type} (D1 D2 : VTop_Stages.aspis_core.digest.Digest32 H)
    (hash : H) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (root : Array U8 32#usize) :
    GExq_BatchSource.stage D1 hash proof p root = GExq_BatchSource.stage D2 hash proof p root := by
  unfold GExq_BatchSource.stage
  rw [batch_source_eq _ (⟨D2.coremarkerCopyInst,D2.digest⟩ : aspis_core.digest.Digest32 H)]
#print axioms batch_loop_eq
#print axioms batch_tree_eq
#print axioms batch_values_eq
#print axioms batch_source_eq
#print axioms batch_eq
#print axioms batch_stage_eq
end AspisR1.NNQ_HostDigest
end
