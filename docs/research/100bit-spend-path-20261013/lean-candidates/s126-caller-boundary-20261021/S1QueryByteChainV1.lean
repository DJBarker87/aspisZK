import S1QueryReadPairProgramV1
import R1QuerySampler
import ExtractedSourceDigestAddresses
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedHashCode.QueryPair
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps

/-- Byte addresses are exactly the source's grouped readParts, flattened.
Both asks use the old state; only the advance reply selects the next state. -/
def pairedBytesProgram {A : Type} (out : List State → List State → A) :
    Nat → State → List State → List State → Program Bytes State A
  | 0,_,blocks,advances => .done (out blocks advances)
  | n+1,state,blocks,advances =>
    .ask (flatten (TranscriptStep.readParts (encodeState state) 1#u8)) fun block =>
      .ask (flatten (TranscriptStep.readParts (encodeState state) 2#u8)) fun advance =>
        pairedBytesProgram out n advance (blocks++[block]) (advances++[advance])

/-- EXACT program equality with the fixed mathematical sampler chain,
including repeated queries, full reply ordering and arbitrary continuation. -/
theorem pairedBytesProgram_eq_model {M Cv A : Type} {L : Nat}
    (p : Params M Cv L) (out : List State → List State → A)
    (n : Nat) (state : State) (blocks advances : List State) :
    pairedBytesProgram out n state blocks advances=
      rename Addr.toBytes (AspisR1.QuerySampler.chain p out n state blocks advances).toProgram := by
  induction n generalizing state blocks advances with
  | zero => rfl
  | succ n ih =>
    simp only [pairedBytesProgram,AspisR1.QuerySampler.chain,Sampler.toProgram,rename,
      SourceDigestAddresses.squeeze_address p,SourceDigestAddresses.advance_address p,state_roundtrip,ih]

#print axioms pairedBytesProgram_eq_model
end AspisR1PublicPreparation.PreparedHashCode.QueryPair
