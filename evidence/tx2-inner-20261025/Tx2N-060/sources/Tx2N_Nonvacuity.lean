import Tx2N_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

/-- The residual writer equation has a physical Vec witness for every model
input. This proves codec consistency, not joint SDK/runtime/source acceptance. -/
theorem writer_equation (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (data : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    ∃ saved : alloc.vec.Vec U8,
      saved = Tx2N_Reader.writer H stored pub (prepared c data rho q)
        (OraclePortCheckpointStateC3.write (model data rho q)).accumulator ∧
      decodeAccumulator (bytesOf saved.val) =
        some (OraclePortCheckpointStateC3.write (model data rho q)).accumulator ∧
      saved.val.length = 1768 := by
  refine ⟨Tx2N_Reader.writer H stored pub (prepared c data rho q)
    (OraclePortCheckpointStateC3.write (model data rho q)).accumulator,rfl,?_,?_⟩
  · rw [Tx2N_Reader.writer_bytes]
    exact decode_written H stored pub (prepared c data rho q) _
      (OraclePortCheckpointStateC3.saved_next _)
  · simp only [Tx2N_Reader.writer,List.length_map,encode_length]

/-- The named powers slot is total on its declared canonical domain. -/
theorem powers_success (N : Usize) (x : Tx2N_Powers.E)
    (canonical : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers x)) :
    ∃ out, Tx2N_Powers.powers N x = ok out := by
  obtain ⟨out,call,_⟩ := Tx2N_Powers.total_exact N x canonical
  exact ⟨out,call⟩

#print axioms writer_equation
#print axioms powers_success
end AspisR1.Tx2N_Nonvacuity
end
