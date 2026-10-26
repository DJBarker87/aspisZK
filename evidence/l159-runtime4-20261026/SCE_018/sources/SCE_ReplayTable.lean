import SCE_Experiment
import OracleProgramReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ReplayTable
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Appending already-known, consistent oracle reads leaves the recovered
oracle unchanged at EVERY address, including addresses outside the trace. -/
theorem oracle_known_suffix (H : Bytes → State) (prefix suffix : List (Bytes × State))
    (consistent : ∀ q ∈ prefix ++ suffix, q.2 = H q.1)
    (known : ∀ a ∈ suffix.map Prod.fst, a ∈ prefix.map Prod.fst) :
    OracleProgramReplay.oracleOf (prefix ++ suffix) = OracleProgramReplay.oracleOf prefix := by
  funext a
  have before : ∀ q ∈ prefix, q.2 = H q.1 :=
    fun q h => consistent q (List.mem_append_left _ h)
  have member : a ∈ (prefix ++ suffix).map Prod.fst ↔ a ∈ prefix.map Prod.fst := by
    rw [List.map_append,List.mem_append]
    exact ⟨fun h => h.elim id (known a),Or.inl⟩
  unfold OracleProgramReplay.oracleOf
  rw [TraceTable.replay_empty_apply H _ consistent,TraceTable.replay_empty_apply H _ before]
  simp only [member]

/-- First-commitment cuts are literal prefixes, so an appended replay cannot
change a cut whose commitment frame already occurred. -/
theorem cut_append (prefix suffix : List (Bytes × State)) (frame : Bytes)
    (read : Read prefix frame) :
    BinRawByteCutRecovery.cut (prefix ++ suffix) frame = BinRawByteCutRecovery.cut prefix frame := by
  induction prefix with
  | nil => cases read
  | cons q tail ih =>
    rcases q with ⟨address,answer⟩
    by_cases same : address = frame
    · subst address
      simp only [BinRawByteCutRecovery.cut,List.cons_append,firstIdx,if_pos,List.take_zero]
    · have rest : Read tail frame := by
        change frame ∈ address :: tail.map Prod.fst at read
        exact (List.mem_cons.mp read).resolve_left (Ne.symm same)
      simpa only [BinRawByteCutRecovery.cut,List.cons_append,firstIdx,if_neg same,
        List.take_succ_cons] using congrArg (List.cons (address,answer)) (ih rest)

#print axioms oracle_known_suffix
#print axioms cut_append
end AspisR1.SCE_ReplayTable
end
