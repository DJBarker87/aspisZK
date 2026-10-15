import R1LiteralTranscript
import R1ProgramSamplerMap

/-! The literal sampler over all finite byte strings. The selected bounded
address type is used only to construct protocol-format calls; oracle addresses
in this sampler are unrestricted byte lists, with no overlength fallback.
This establishes execution and independent-answer transport only. The decoder,
first-read injection, shared-oracle reduction and source refinement remain
separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralByteSampler

open FS FS2 FS2.Duplex
open AspisV8R19 AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

def samp (i : Nat) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Sampler Bytes State LiteralTranscript.Challenge :=
  ProgramSamplerMap.map Addr.toBytes (LiteralTranscript.samp i P m)

theorem independentMean_eq (i : Nat) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (obs : LiteralTranscript.Challenge → ℚ) :
    independentMean (samp i P m).toProgram (fun v => obs v.2) =
      independentMean (LiteralTranscript.samp i P m).toProgram (fun v => obs v.2) :=
  ProgramSamplerMap.independentMean_map _ _ obs

theorem eval_eq (H : Bytes → State) (i : Nat) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) :
    eval H (samp i P m).toProgram =
      OracleProgramOps.mapView Addr.toBytes
        (eval (fun a => H a.toBytes) (LiteralTranscript.samp i P m).toProgram) := by
  unfold samp ProgramSamplerMap.map
  rw [ProgramSamplerMap.toProgram_fromProgram]
  exact OracleProgramOps.eval_rename _ _ _

#print axioms independentMean_eq
#print axioms eval_eq

end AspisR1.LiteralByteSampler
end
