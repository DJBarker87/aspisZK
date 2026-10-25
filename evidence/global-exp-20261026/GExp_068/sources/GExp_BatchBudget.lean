import GExp_BatchTreeBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_BatchBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws
attribute [local irreducible] Port9OR_BatchTree.code

theorem values (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array Digest 3#usize) (which : Usize) :
    count 11232 (Port9OR_Batch.values base D hash proof queries roots which) := by
  unfold Port9OR_Batch.values
  repeat' first
    | (solve | apply pure_count)
    | (solve | apply lift_count)
    | (apply lift_bind_count;intro x)
    | (query_count_then_for 3744 Port9OR_BatchTree.code
       <;> first | omega | (solve | apply GExp_BatchTreeBudget.tree) | intro x)
    | split

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array Digest 2#usize) (root : Digest) (which : Usize) :
    count 11232 (SdkC_BatchSource.code D hash proof queries roots root which) := by
  unfold SdkC_BatchSource.code
  apply lift_bind_count;intro r0
  apply lift_bind_count;intro r1
  exact values _ _ _ _ _ _ _

theorem map {Err : Type} (f : AspisR1Stage2.verifier.Error → Err)
    (p : Code (core.result.Result Unit AspisR1Stage2.verifier.Error))
    (n : Nat) (bound : count n p) : count n (SdkC_BatchSource.mapCode f p) := by
  unfold SdkC_BatchSource.mapCode
  apply then_count (p:=p) (cost:=n)
  · omega
  · exact bound
  · intro result
    exact pure_count _ _

theorem current (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest) :
    count 11232 (SdkC_BatchSource.currentCode hashv proof p root) :=
  map _ _ _ (source _ _ _ _ _ _ _)

theorem stage (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Digest) :
    count 11232 (SdkC_BatchSource.stageCode hashv proof p root) :=
  map _ _ _ (source _ _ _ _ _ _ _)

#print axioms values
#print axioms source
#print axioms map
#print axioms current
#print axioms stage
end AspisR1.GExp_BatchBudget
end
