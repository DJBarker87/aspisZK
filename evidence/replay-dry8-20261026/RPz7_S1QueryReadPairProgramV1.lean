import RPz7_S1PreparedOracleProgramLawsV1
import S1QueryArrayOperationsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode.QueryPair
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisS1QueryArrayOperations
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks8 := Array Bytes32 8#usize

/-- Exact source read-argument construction, including every to_slice lift. -/
def readState {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Bytes32) (tag : U8) : Code Bytes32 := do
  let s ← lift (Array.to_slice state)
  let t ← lift (Array.to_slice (Array.make 1#usize [tag]))
  let parts ← lift (Array.to_slice (Array.make 2#usize [s,t]))
  effects.digest D hash parts

theorem readState_program {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Bytes32) (tag : U8) :
    oracleProgram (readState D hash state tag)=
      Program.ask (flatten (TranscriptStep.readParts state tag))
        (fun reply => .done (ok (encodeState reply))) := by
  simp only [readState,oracleProgram_bind,oracleProgram_lift,oracleProgram_digest,
    lift,AspisV8R19.OracleProgramOps.bind,continueOracle]
  rfl

/-- A source-shaped pair step. The next state is read back from the SAME
updated advances array; it is not supplied as an independent witness. -/
def pairStep {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Bytes32) (blocks advances : Blocks8) (i : Usize) : Code (Bytes32 × Blocks8 × Blocks8) := do
  let b ← readState D hash state 1#u8
  let blocks1 ← Array.update blocks i b
  let x ← readState D hash state 2#u8
  let advances1 ← Array.update advances i x
  let next ← Array.index_usize advances1 i
  pure (next,blocks1,advances1)

theorem index_set {A : Type} {n : Usize} (a : Array A n) (i : Usize) (value : A)
    (bound : i.val<n.val) : Array.index_usize (a.set i value) i=ok value := by
  rw [index_total _ _ bound]
  simp only [Array.set_val_eq,List.getElem_set_self]

/-- TOTAL source-model administrative operations for i<8, and exactly two
ordered reads of the old state. No update/read success is a premise. -/
theorem pairStep_program {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Bytes32) (blocks advances : Blocks8) (i : Usize) (bound : i.val<8) :
    oracleProgram (pairStep D hash state blocks advances i)=
      Program.ask (flatten (TranscriptStep.readParts state 1#u8)) (fun b =>
        Program.ask (flatten (TranscriptStep.readParts state 2#u8)) (fun x =>
          .done (ok (encodeState x,blocks.set i (encodeState b),advances.set i (encodeState x))))) := by
  have writes : ∀ (a : Blocks8) (value : Bytes32), Array.update a i value=ok (a.set i value) :=
    fun a value => update_total a i value bound
  have reads : ∀ (a : Blocks8) (value : Bytes32), Array.index_usize (a.set i value) i=ok value :=
    fun a value => index_set a i value bound
  unfold pairStep
  simp only [oracleProgram_bind,readState_program,oracleProgram_lift,oracleProgram_pure,
    writes,reads,AspisV8R19.OracleProgramOps.bind,continueOracle]

#print axioms index_set
#print axioms readState_program
#print axioms pairStep_program
end AspisR1PublicPreparation.PreparedHashCode.QueryPair
