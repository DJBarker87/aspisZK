import RPv_FJs_PreparedPoint
import RPv_FIo_ConcreteDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_PreparedAlphas
open Aeneas Aeneas.Std Result AspisR1Stage2
open FIo_FieldBridge (NE wide)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem decoded (x : Stage2Finish.E) :
    AspisR1CurrentWide.Proof.decodeWide (wide (FIo_Install.toE x))=CheckpointBytes5Output.ofE x := by
  rw [←FIo_ConcreteDictionary.decoded,FIo_Install.from_to]

theorem values (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am)
    (alpha : Slice Stage2Finish.E)
    (prefixRun : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Stage2Finish.E)) p.alpha ⟨2#usize⟩=ok alpha)
    (a0 a1 : NE)
    (h0 : Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0)
    (h1 : Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1) :
    AspisR1CurrentWide.Proof.decodeWide (wide a0)=pm.alpha 0 ∧
    AspisR1CurrentWide.Proof.decodeWide (wide a1)=pm.alpha 1 := by
  have vals := (FJr_AlphaPrefix.value p.alpha alpha (by decide) prefixRun).1
  have av : alpha.val=[CheckpointBytes4ReaderFields.sourceE (pm.alpha 0),
      CheckpointBytes4ReaderFields.sourceE (pm.alpha 1)] := by
    rw [vals,fields.alpha];rfl
  have r0 : Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=
      ok (FIo_Install.toE (CheckpointBytes4ReaderFields.sourceE (pm.alpha 0))) := by
    simp [Slice.index_usize,FIo_Install.toSlice,av]
  have r1 : Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=
      ok (FIo_Install.toE (CheckpointBytes4ReaderFields.sourceE (pm.alpha 1))) := by
    simp [Slice.index_usize,FIo_Install.toSlice,av]
  have e0 := Result.ok.inj (h0.symm.trans r0)
  have e1 := Result.ok.inj (h1.symm.trans r1)
  rw [e0,e1,decoded,decoded,CheckpointBytes5Output.ofE_source,CheckpointBytes5Output.ofE_source]
  exact ⟨rfl,rfl⟩

#print axioms decoded
#print axioms values
end AspisR1.FJs_PreparedAlphas
end
