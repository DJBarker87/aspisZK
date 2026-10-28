import AspisR1EffectCallers27.Funs
import R1Z.ProverCommitCoinSequence27
/-! Concrete effect dictionary and source-shaped call trees for the shared
semantic/circle helper and the suffix block. These expose returned hash state. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEffectCallers27
open Aeneas Aeneas.Std Result AspisR1EffectCallers27
open ProverCommitCoinTape27 ProverCommitCoinCall27 ProverCommitCoinSequence27
attribute [local instance] Classical.propDecidable
abbrev Bytes32 := ProverCommitCoinCall27.Bytes32
abbrev Parts := ProverCommitOracleEffect26.Parts

def hash : AspisR1EffectCallers27.Digest32 Machine :=
  ⟨AspisR1CoinEffect27.CoinOracle.Insts.Effect27EffectDigest32CoinState.digest mapRecording⟩

def absorbParts (state : Bytes32) (row : U8) (framed : Slice U8) : Parts :=
  Array.to_slice (Array.make 3#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,U8.wrapping_add 160#u8 row]),framed])

def readParts (state : Bytes32) (side : U8) : Parts :=
  Array.to_slice (Array.make 2#usize [Array.to_slice state,
    Array.to_slice (Array.make 1#usize [side])])

abbrev SemanticValue := (core.result.Result Bytes32 AspisR1EffectCallers27.Error) × Bytes32 × U8

def semanticProgram (state : Bytes32) (nextRow row : U8) (framed : Slice U8) :
    Program Parts Bytes32 SemanticValue :=
  if row != nextRow then .done (.Err (.RowOrder nextRow row),state,nextRow)
  else .call (absorbParts state row framed) fun absorbed =>
    .call (readParts absorbed 1#u8) fun block =>
    .call (readParts absorbed 2#u8) fun advanced =>
    .done (.Ok block,advanced,U8.wrapping_add nextRow 1#u8)

def semanticOutput (r : Run SemanticValue) :
    (core.result.Result Bytes32 AspisR1EffectCallers27.Error) × SemanticTranscript Machine :=
  (r.value.1,⟨r.value.2.1,r.state,r.value.2.2⟩)

/-- The exact extracted semantic/circle three-read helper, including mismatch
rejection with no reads, returns precisely the threaded oracle effects. -/
theorem semantic_call (s : SemanticTranscript Machine) (row : U8) (framed : Slice U8) :
    SemanticTranscript.sample_block_validated hash s row framed =
      ok (semanticOutput (referenceRun (semanticProgram s.state s.next_row row framed) s.hash)) := by
  by_cases same : row = s.next_row
  · subst row
    simp only [SemanticTranscript.sample_block_validated,semanticProgram,bne_self_eq_false,
      Bool.false_eq_true,if_false,hash,call_exact,bind_tc_ok,lift,
      referenceRun,absorbParts,readParts,semanticOutput,Aeneas.Std.uncurry]
  · have different : (row != s.next_row) = true := by simp [same]
    simp only [SemanticTranscript.sample_block_validated,semanticProgram,different,
      if_true,semanticOutput,referenceRun]

def suffixAbsorbParts (state : Bytes32) (row : U8) (payload : Slice U8) : Parts :=
  Array.to_slice (Array.make 4#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,U8.wrapping_add 160#u8 row]),
    Array.to_slice (core.num.U32.to_le_bytes (UScalar.cast .U32 (Slice.len payload))),payload])

def blockProgram (state : Bytes32) (row : U8) (payload : Slice U8) :
    Program Parts Bytes32 (Bytes32 × Bytes32) :=
  .call (suffixAbsorbParts state row payload) fun absorbed =>
  .call (readParts absorbed 1#u8) fun block =>
  .call (readParts absorbed 2#u8) fun advanced =>
  .done (block,advanced)

def blockOutput (r : Run (Bytes32 × Bytes32)) : Bytes32 × Transcript Machine :=
  (r.value.1,⟨r.value.2,r.state⟩)

theorem block_call (s : Transcript Machine) (row : U8) (payload : Slice U8) :
    Transcript.block hash s row payload =
      ok (blockOutput (referenceRun (blockProgram s.state row payload) s.hash)) := by
  simp only [Transcript.block,Transcript.absorb,hash,call_exact,bind_tc_ok,lift,
    referenceRun,blockProgram,suffixAbsorbParts,readParts,blockOutput,Aeneas.Std.uncurry]

/-- This is the concrete reference step, not a supplied execution-equality field. -/
def referenceHash : AspisR1EffectCallers27.Digest32 Machine :=
  ⟨fun s parts => ok (expected s parts)⟩

theorem dictionary_exact : hash = referenceHash := by
  unfold hash referenceHash
  congr 1
  funext s parts
  exact call_exact s parts

/-- All sixteen eager query reads and the absorb use exactly the returned
reference effects. No query reads, failures or returned hash state are dropped. -/
theorem query_effects (s : Transcript Machine) (row : U8) (payload : Slice U8) :
    Transcript.materialize hash s row payload =
      Transcript.materialize referenceHash s row payload := by
  rw [dictionary_exact]

theorem semantic_history_length (state : Bytes32) (nextRow row : U8) (framed : Slice U8)
    (s : Machine) :
    (referenceRun (semanticProgram state nextRow row framed) s).history.length =
      if row=nextRow then 3 else 0 := by
  by_cases same : row=nextRow
  · subst row
    simp [semanticProgram,referenceRun]
  · simp [semanticProgram,referenceRun,same]

theorem block_history_length (state : Bytes32) (row : U8) (payload : Slice U8) (s : Machine) :
    (referenceRun (blockProgram state row payload) s).history.length = 3 := by
  simp [blockProgram,referenceRun]

#print axioms semantic_call
#print axioms block_call
#print axioms dictionary_exact
#print axioms query_effects
#print axioms semantic_history_length
#print axioms block_history_length
end R1Z.ProverCommitEffectCallers27
