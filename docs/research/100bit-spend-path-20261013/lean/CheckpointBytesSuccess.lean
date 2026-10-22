import OraclePortCkptAbiSourceFields
import OraclePortCkptAbi5Weights

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.CheckpointBytesSuccess
open AspisR1Stage2 OraclePortCkptAbiSourceFields

/-- Source success itself supplies successful allocation and the exact
allocation-to-weight-reader dependency. No availability premise is added. -/
theorem source_allocation_succeeded (ops : ResumeOps) {H : Type}
    (digestInst : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps ops digestInst ck proof pub v hash = ok (.Ok (p,a))) :
    ∃ n zero allocated at1 end1, ∃ powerReader : verifier.Reader,
      ops.finalLen v = ok n ∧ ops.zeroK = ok zero ∧
      ops.filled n zero = ok (.Ok allocated) ∧
      ops.readWeights ck powerReader.at allocated = ok (.Ok (a.weights,at1)) ∧
      Slice.len ck - 32#usize = ok end1 ∧ at1 = end1 := by
  obtain ⟨f⟩ := successful_fields ops digestInst ck proof pub v hash p a success
  exact ⟨f.finalLength,f.zero,f.allocated,f.finalAt,f.checksumEnd,f.rPower,
    f.lengthCall,f.zeroCall,f.allocation,f.weightsRead,f.checksumEndCall,f.cursor⟩

/-- Content semantics conditional on a successful fallible allocation/write.
The input reservation bit is derived from the result, rather than assumed. -/
theorem successful_overwrite {T : Type} (n : Usize) (zero : T) (reserved : Bool)
    (values : List T) (length : values.length = n.val) (out : Slice T × Nat)
    (success : OraclePortCkptAbi5Weights.allocatedOverwrite n zero reserved values = ok (.ok out)) :
    reserved = true ∧ out.1.val = values ∧ out.2 = n.val := by
  rw [OraclePortCkptAbi5Weights.allocated_overwrite_exact n zero reserved values length] at success
  cases reserved with
  | false => cases success
  | true =>
    simp only [↓reduceIte] at success
    have eqn := Except.ok.inj (Result.ok.inj success)
    subst out
    exact ⟨rfl,rfl,rfl⟩

#print axioms source_allocation_succeeded
#print axioms successful_overwrite
end AspisR1.CheckpointBytesSuccess
