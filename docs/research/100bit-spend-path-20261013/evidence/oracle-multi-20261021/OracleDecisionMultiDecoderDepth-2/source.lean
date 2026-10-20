import OracleDecisionMultiDecoder
import OracleDecisionMultiProfile

/-! Lift the one-start example to the deployed binary depth, using symbolic
padding. It is a small authentication example, not a 57607-byte frozen proof. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiDecoderDepth
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionMultiTree OracleDecisionMultiProfile OracleDecisionMultiDecoder
open DecodedFirstReadUnionBound

def five : State := fun _ => 5
def upper : Bytes := BinMerkle32Path.nodeInput (children five zero)
def upperAddr : Addr L := Addr.ofBytes upper (by
  change (BinMerkle32Path.nodeInput _).length ≤ L
  rw [BinMerkle32Path.nodeInput_length]; decide)

theorem upper_rejected (T : Table Bytes State) : RecordedBinaryExperimentBin.dec upper T = none := by
  have hc : CanonicalByteAddress.Canonical upperAddr := by
    unfold upperAddr; apply CanonicalByteAddress.canonical_ofBytes
  have hb : upperAddr.toBytes = upper := Addr.toBytes_ofBytes _ _
  rw [← hb]
  apply BinHonestStartFrames.reject_other upperAddr hc
  · rw [parseAbsorb, hb]
    have hm : upper.getD 32 1 ≠ 0 := by decide
    exact if_neg (fun h => hm h.2)
  · rw [hb]
    change (BinMerkle32Path.nodeInput _).length < 75
    rw [BinMerkle32Path.nodeInput_length]
    decide

theorem upper_starts (T : Table Bytes State) (d : State) :
    decoderFirstReads RecordedBinaryExperimentBin.dec T [(upper,d)] = 0 := by
  simp only [decoderFirstReads, upper_rejected, ne_eq, not_true_eq_false,
    and_false, if_false, Nat.add_zero]

theorem pad_root (H : Bytes → State) (hLeaf : H leaf = zero)
    (hNode : H node = five) (hUpper : H upper = five) (n : Nat) :
    root H (pad n exampleTree) = five := by
  induction n with
  | zero =>
      change H (BinMerkle32Path.nodeInput (children (H leaf) right)) = five
      rw [hLeaf]
      exact hNode
  | succ n ih =>
      change H (BinMerkle32Path.nodeInput (children (root H (pad n exampleTree)) zero)) = five
      rw [ih]
      exact hUpper

theorem pad_starts (H : Bytes → State) (hLeaf : H leaf = zero)
    (hNode : H node = five) (hUpper : H upper = five) (n : Nat) :
    decoderFirstReads RecordedBinaryExperimentBin.dec table
      (eval H (execute (pad n exampleTree))).1 = 1 := by
  induction n with
  | zero =>
      change decoderFirstReads RecordedBinaryExperimentBin.dec table
        (eval H (execute exampleTree)).1 = 1
      have ht := terminal_start_count H hLeaf
      simpa only [terminal, OracleDecisionPrereqPaths.readFrames, List.nil_append,
        verifyTrees, eval_bind, eval, List.append_nil] using ht
  | succ n ih =>
      simp only [pad, execute, eval_bind, eval, execute_root,
        pad_root H hLeaf hNode hUpper]
      change decoderFirstReads RecordedBinaryExperimentBin.dec table
        ((eval H (execute (pad n exampleTree))).1 ++ [(upper,H upper)]) = 1
      rw [decoderFirstReads_append, upper_starts]
      omega

/-- Depth 1 + 17 unary shared levels. Exactly one fresh decoder start. -/
theorem depth18_terminal_starts (H : Bytes → State) (hLeaf : H leaf = zero)
    (hNode : H node = five) (hUpper : H upper = five) :
    decoderFirstReads RecordedBinaryExperimentBin.dec table
      (eval H (terminal [⟨pad 17 exampleTree,five⟩] [] [])).1 = 1 := by
  simpa only [terminal, OracleDecisionPrereqPaths.readFrames, List.nil_append,
    verifyTrees, eval_bind, eval, List.append_nil] using pad_starts H hLeaf hNode hUpper 17

def exampleHash (b : Bytes) : State := (table b).getD five

theorem exampleHash_agrees (b : Bytes) (v : State) (h : table b = some v) :
    exampleHash b = v := by simp only [exampleHash, h, Option.getD_some]

theorem exampleHash_values : exampleHash leaf = zero ∧ exampleHash node = five ∧
    exampleHash upper = five := by
  have hl := byte_lengths
  have hu : upper.length = 65 := BinMerkle32Path.nodeInput_length _
  have h0 : upper ≠ initial.toBytes := by intro he; have := congrArg List.length he; omega
  have h1 : upper ≠ row0.toBytes := by intro he; have := congrArg List.length he; omega
  have h2 : upper ≠ advanced.toBytes := by intro he; have := congrArg List.length he; omega
  have h3 : upper ≠ leaf := by intro he; have := congrArg List.length he; omega
  have ht : table upper = none := by simp only [table, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
  exact ⟨exampleHash_agrees leaf zero leaf_cached,
    by simp only [exampleHash,node_fresh,Option.getD_none],
    by simp only [exampleHash,ht,Option.getD_none]⟩

/-- A fully instantiated oracle, agreeing with every cell of the supporting
finite table. No oracle-value hypothesis remains in this example. -/
theorem concrete_depth18_count :
    decoderFirstReads RecordedBinaryExperimentBin.dec table
      (eval exampleHash (terminal [⟨pad 17 exampleTree,five⟩] [] [])).1 = 1 :=
  depth18_terminal_starts exampleHash exampleHash_values.1 exampleHash_values.2.1
    exampleHash_values.2.2

#print axioms exampleHash_agrees
#print axioms exampleHash_values
#print axioms concrete_depth18_count
#print axioms upper_rejected
#print axioms upper_starts
#print axioms pad_root
#print axioms pad_starts
#print axioms depth18_terminal_starts
end AspisR1.OracleDecisionMultiDecoderDepth
end
