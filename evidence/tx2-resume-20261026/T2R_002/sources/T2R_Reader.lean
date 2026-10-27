import Cons_Native
import Tx2N_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_Reader
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- The same installed op18 return supplies the variant and both alpha reads.
No encoding or model-state equation is needed for these physical facts. -/
theorem observations {C Hash : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : (Tx2N_Execution.control base reserved query geo).op18 D checkpoint proof pub .S2 hash =
      ok (.Ok (p,a))) :
    p.variant = .S2 ∧ ∃ (alpha0 alpha1 : Stage2Finish.E) (alphas : Slice Stage2Finish.E),
      Array.index_usize p.alpha 0#usize = ok alpha0 ∧
      Array.index_usize p.alpha 1#usize = ok alpha1 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Stage2Finish.E)) p.alpha
        { «end» := 2#usize } = ok alphas := by
  have source := Tx2N_Install.reader_success base reserved query D hash checkpoint proof pub .S2 p a success
  obtain ⟨fields⟩ := CheckpointBytes4Ops.successful_fields reserved _ checkpoint proof pub .S2 hash p a source
  refine ⟨fields.variant,fields.alpha0,fields.alpha1,p.alpha.to_slice,?_,?_,?_⟩
  · simp [fields.alpha,Array.index_usize]
  · simp [fields.alpha,Array.index_usize]
  · simp [fields.alpha,core.array.Array.index,core.ops.index.IndexSlice,
      core.slice.index.SliceIndexRangeToUsizeSlice]

#print axioms observations
end AspisR1.T2R_Reader
end
