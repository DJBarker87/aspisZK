import R1Z.ProverCommitStreamPack25
import R1Z.ProverCommitJointHistory19
/-! Real finite-ROM marginal for all rejection words on stream 3. The
coupling starts from model nonzero coins times independent fuel, packs their
actual consumed prefixes and replaces those coordinates of one common table.
Observer histories are protected by the existing seedGuess event. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitProductOracle25
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.LawTransport
open R1Z.GamesR1 R1Z.CouplingR1PBin ProverCommitStreamPack25 ProverCommitProduct25
open ProverCommitJointHistory19 ProverCommitSeedEvent19
attribute [local instance] Classical.propDecidable
attribute [local irreducible] tripleEquiv raw swap
private def answerFinite : Fintype OracleAnswer := inferInstance
attribute [local instance] answerFinite
attribute [local irreducible] answerFinite
local instance zeroDecision : DecidablePred (fun a : OracleAnswer => a ≠ 0) :=
  fun _ => Classical.propDecidable _
abbrev LocalInput := Trio (NZ (0 : OracleAnswer)) × Trio (Fin 5 → OracleAnswer)
abbrev Input := Fin 8 → LocalInput
abbrev Coord := Fin 8 × Fin 15
local instance coordDecision : DecidableEq Coord := fun _ _ => Classical.propDecidable _

def flatten : (Fin 8 → Fin 15 → OracleAnswer) ≃ (Coord → OracleAnswer) where
  toFun t i := t i.1 i.2
  invFun t a i := t (a,i)
  left_inv _ := rfl
  right_inv _ := rfl

def words (p : Input) : Coord → OracleAnswer :=
  fun i => tripleEquiv (0 : OracleAnswer) 5 (raw (0 : OracleAnswer) 5 (p i.1)) i.2

theorem words_uniform : MP words := by
  have one : MP (fun p : LocalInput => tripleEquiv (0 : OracleAnswer) 5
      (raw (0 : OracleAnswer) 5 p)) := by
    intro test
    exact (QueryScanIdealHistory.mean_fintype_transport _ _ _).trans
      (source_stream_marginal (0 : OracleAnswer) 5 test)
  have h := mp_pi one 8
  intro test
  exact (QueryScanIdealHistory.mean_fintype_transport _ _ _).trans
    ((h (fun t => test (flatten t))).trans
      ((QueryScanIdealHistory.mean_fintype_transport _ _ _).trans (mp_equiv flatten test)))

def key (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer) (i : Coord) :
    RomFiniteBin.Address bound :=
  ProverCommitSimulatorOracle18.key (count := 15) bound fits seed (i.1,3,i.2)

theorem key_injective (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer) :
    Function.Injective (key bound fits seed) := by
  intro i j same
  have eq := ProverCommitSimulatorOracle18.key_injective (count := 15)
    (by norm_num) bound fits seed same
  apply Prod.ext
  · exact congrArg (fun z : ProverCommitSimulatorOracle18.Index 15 => z.1) eq
  · exact congrArg (fun z : ProverCommitSimulatorOracle18.Index 15 => z.2.2) eq

def table (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (p : Input × (RomFiniteBin.Address bound → OracleAnswer)) :
    RomFiniteBin.Address bound → OracleAnswer :=
  replaceTable (key bound fits seed) (key_injective bound fits seed) (words p.1) p.2

/-- The entire retained source oracle, not only the successful nonce, has
its exact uniform distribution. No source-law or coupling premise is supplied. -/
theorem source_oracle_uniform (bound : Nat) [Fintype (RomFiniteBin.Address bound)]
    (fits : 65 ≤ bound) (seed : OracleAnswer) : MP (table bound fits seed) := by
  have h := mp_prodMap words_uniform (show MP (id :
    (RomFiniteBin.Address bound → OracleAnswer) → _) from fun _ => rfl)
  intro test
  exact (h (fun p => test (replaceTable (key bound fits seed)
    (key_injective bound fits seed) p.1 p.2))).trans
      ((QueryScanIdealHistory.mean_fintype_transport _ _ _).trans
        (replacement_uniform (key bound fits seed) (key_injective bound fits seed) test))

/-- Each actual stream-3 source coordinate carries the packed raw word. -/
theorem source_at (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (p : Input × (RomFiniteBin.Address bound → OracleAnswer)) (i : Coord) :
    table bound fits seed p (key bound fits seed i) = words p.1 i := replace_at _ _ _ _ i

/-- Full ordered adaptive observer trace, including repeated queries and
termination, agrees outside the existing seed namespace event. -/
theorem observer_history (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (p : Input × (RomFiniteBin.Address bound → OracleAnswer)) (program : OProg) (fuel : Nat)
    (fresh : ¬ seedGuess (runLog program (RomFiniteBin.lookup bound p.2) fuel) seed) :
    runLog program (RomFiniteBin.lookup bound (table bound fits seed p)) fuel =
      runLog program (RomFiniteBin.lookup bound p.2) fuel := by
  apply runLog_agrees
  intro e member
  unfold RomFiniteBin.lookup
  split
  · next addr decoded =>
    apply replace_off
    rintro ⟨i,same⟩
    have hb := RomFiniteBin.encode_decode bound e.1 addr decoded
    have hkey := congrArg Subtype.val same
    apply fresh
    refine ⟨e,member,?_⟩
    rw [← hb,← hkey]
    exact source_point seed _ _ _
  · rfl

#print axioms words_uniform
#print axioms key_injective
#print axioms source_oracle_uniform
#print axioms source_at
#print axioms observer_history
end R1Z.ProverCommitProductOracle25
