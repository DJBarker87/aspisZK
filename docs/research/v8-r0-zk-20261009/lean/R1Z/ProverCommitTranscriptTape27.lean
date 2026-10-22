import R1Z.ProverCommitCursorMarginal27
/-! The native CoinOracle's 115 pre-drawn stream-0 answers come from the
existing product oracle, not a newly sampled tape. Stream-3 rejection packing
leaves all of these coordinates unchanged. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTranscriptTape27
open R0Z R0Z.FsStatement R0Z.LawTransport
open ProverCommitCoinTape27 ProverCommitCursorMarginal27 ProverCommitProductOracle25
attribute [local instance] Classical.propDecidable
private def answerFinite : Fintype OracleAnswer := inferInstance
attribute [local instance] answerFinite
attribute [local irreducible] answerFinite
private def inputFinite : Fintype Input := inferInstance
attribute [local instance] inputFinite
attribute [local irreducible] inputFinite

abbrev Tab (bound : Nat) := RomFiniteBin.Address bound → OracleAnswer

def transcriptKey (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (cursor : Fin 115) : RomFiniteBin.Address bound :=
  ProverCommitSimulatorOracle18.key bound fits seed (attempt,0,cursor)

theorem stream_disjoint (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (cursor : Fin 115) (i : Coord) :
    key bound fits seed i ≠ transcriptKey bound fits seed attempt cursor := by
  intro same
  have lifted : ProverCommitSimulatorOracle18.key (count := 115) bound fits seed
      (i.1,3,⟨i.2.val,lt_of_lt_of_le i.2.isLt (by decide)⟩) =
      ProverCommitSimulatorOracle18.key bound fits seed (attempt,0,cursor) := by
    apply Subtype.ext
    exact congrArg Subtype.val same
  have eq := ProverCommitSimulatorOracle18.key_injective (count := 115)
    (by norm_num) bound fits seed lifted
  have impossible := congrArg (fun j : ProverCommitSimulatorOracle18.Index 115 => j.2.1.val) eq
  norm_num at impossible

/-- Stream-0 answers are precisely the retained table's answers in the product. -/
theorem transcript_unchanged (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (p : Input × Tab bound) (attempt : Fin 8) (cursor : Fin 115) :
    table bound fits seed p (transcriptKey bound fits seed attempt cursor) =
      p.2 (transcriptKey bound fits seed attempt cursor) := by
  apply ProverCommitJointHistory19.replace_off
  rintro ⟨i,same⟩
  exact stream_disjoint bound fits seed attempt cursor i same

/-- Exact finite-tape zero fallback, indexed by the explicit cursor. -/
def coins (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (t : Tab bound) (cursor : Nat) : OracleAnswer :=
  if h : cursor < 115 then t (transcriptKey bound fits seed attempt ⟨cursor,h⟩) else 0

theorem product_coins (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (p : Input × Tab bound) :
    coins bound fits seed attempt (table bound fits seed p) =
      coins bound fits seed attempt p.2 := by
  funext cursor
  unfold coins
  split
  · exact transcript_unchanged bound fits seed p attempt _
  · rfl

/-- The complete effectful execution has the uniform source-table law, with
its cursor and recorded table retained in the tested observation. -/
theorem execution_law {Value : Type} (bound : Nat) [Fintype (RomFiniteBin.Address bound)]
    (fits : 65 ≤ bound) (seed : OracleAnswer) (attempt : Fin 8) (recording : Bool)
    (program : Program (List UInt8) OracleAnswer Value)
    (test : Execution (List UInt8) OracleAnswer Value → ℚ) :
    mean (fun p : Input × Tab bound => test (run reference program
      (initial (coins bound fits seed attempt (table bound fits seed p)) recording))) =
    mean (fun t : Tab bound => test (run reference program
      (initial (coins bound fits seed attempt t) recording))) := by
  exact (QueryScanIdealHistory.mean_fintype_transport _ _ _).trans
    ((source_oracle_uniform bound fits seed
      (fun t => test (run reference program
        (initial (coins bound fits seed attempt t) recording)))).trans
      (QueryScanIdealHistory.mean_fintype_transport _ _ _))

#print axioms stream_disjoint
#print axioms transcript_unchanged
#print axioms product_coins
#print axioms execution_law
end R1Z.ProverCommitTranscriptTape27
