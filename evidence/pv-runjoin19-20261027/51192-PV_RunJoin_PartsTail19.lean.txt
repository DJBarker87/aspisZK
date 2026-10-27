import R1Z.PV_Src_Forest_PartsComplete
import R1Z.PV_RunJoin_ReferenceFixtureResults
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PartsTail19
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments

theorem path_total (w : RW) (p : RP) : ∃ b, pathR (wordWitness w) (wordPublic p) = ok b := by
  unfold pathR
  obtain ⟨b,hb,_⟩ := path_block_loop (wordWitness w).bits
    (curArr (wordWitness w) (wordPublic p)) (leftArr (wordWitness w) (wordPublic p))
    (rightArr (wordWitness w) (wordPublic p)) 24 0#usize (Array.repeat 1536#usize 0#u32) (by simp)
  exact ⟨b,by rw [R0WriterCopies.write_path_block];exact hb⟩
#print axioms path_total

theorem aux_total (w : RW) (p : RP) (hw : WitnessOk (wordWitness w)) :
    ∃ b, auxR (wordWitness w) (wordPublic p) = ok b := by
  have hv : ∀ i, i < 3 → ((valuesArr (wordWitness w)).val[i]!).val < 2^30 := by
    intro i hi
    interval_cases i
    · exact hw.values.1
    · exact hw.values.2.1
    · exact hw.values.2.2
  obtain ⟨a,ha,_⟩ := value_block (valuesArr (wordWitness w)) hv
  obtain ⟨b,hb,_⟩ := occ_row a 9#usize (by decide) (inRec (wordWitness w))
  obtain ⟨c,hc,_⟩ := occ_row b 10#usize (by decide) (outRec (wordWitness w) (wordPublic p))
  refine ⟨c,?_⟩
  rw [auxR,R0WriterCopies.write_aux_block,ha]
  simp only [bind_tc_ok,hb,hc]
#print axioms aux_total
end R1Z.PV_RunJoin_PartsTail19
