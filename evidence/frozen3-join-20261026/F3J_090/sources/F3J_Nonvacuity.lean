import F3J_BlockCodeValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def digest (state : Array U8 32#usize) : aspis_core.Digest32 Unit where
  digest := fun _ _ => ok state

theorem backend (state : Array U8 32#usize) :
    Tx1DigestLog.ByteOracleBackend (digest state) (fun _ => decodeState state) := by
  intro q actual
  obtain ⟨hash,parts,out,same,returned⟩ := actual
  have equal : state=out := Result.ok.inj returned
  subst out
  subst q
  rfl

theorem sample (state : Array U8 32#usize) (framed : Slice U8) :
    r1_wire.SemanticTranscript.sample_block_validated (digest state)
      ⟨state,(),25#u8⟩ 25#u8 framed=ok (.Ok state,⟨state,(),26#u8⟩) := by
  rw [TranscriptStep.step_of_add (digest state) ⟨state,(),25#u8⟩ 25#u8 185#u8 26#u8 framed
    rfl (by decide) (by decide)]
  rfl

theorem issued (state : Array U8 32#usize) (framed : Slice U8) :
    (observe (run (S1SemanticCode.sampleBlock (digest state) ⟨state,(),25#u8⟩ 25#u8 framed)).1).length=3 := by
  obtain ⟨calls⟩ := F3J_BlockCalls.from_success (digest state) ⟨state,(),25#u8⟩ ⟨state,(),26#u8⟩
    25#u8 framed state (by decide) (sample state framed)
  rw [F3J_BlockCode.sample calls]
  rfl

#print axioms backend
#print axioms sample
#print axioms issued
end AspisR1.F3J_Nonvacuity
end
