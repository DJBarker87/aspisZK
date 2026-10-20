import OracleDecisionPrereqSampler
import OracleDecisionFeasibilityBridge

/-! An explicit independent-path decision. Roots are compared, not hashed a
second time: the last node of each path already hashes the Merkle root.
Extra frame/checksum calls are explicit byte inputs, never free operations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqPaths
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionFeasibilityCore OracleDecisionFeasibilityMerkle
open BinMerkle32Path

structure Opening where
  slots : List (Fin 2)
  path : Path slots
  tag : BinMerkle32Path.Byte
  packed : Bytes
  salt : Bytes
  root : State

def Opening.leaf (o : Opening) : Bytes := BinMerkle32Leaf.leafInput o.tag o.packed o.salt

def checkAll : List Opening → Program Bytes State Bool
  | [] => .done true
  | o :: os => bind (checkPath o.path o.leaf o.root) fun b =>
      bind (checkAll os) fun c => .done (b && c)

def readFrames : List Bytes → Program Bytes State Unit
  | [] => .done ()
  | a :: rest => .ask a fun _ => readFrames rest

def terminal (os : List Opening) (frames : List Bytes) : Program Bytes State Bool :=
  bind (readFrames frames) fun _ => checkAll os

def decision (os : List Opening) (frames : List Bytes) : Decision := fun _ _ => terminal os frames

def pathCalls (os : List Opening) : Nat := (os.map fun o => o.slots.length + 1).sum

def B_V (queries depth frameReads : Nat) : Nat := 115 + 3 * queries * (depth + 1) + frameReads

theorem checkAll_length (os : List Opening) (H : Bytes → State) :
    (eval H (checkAll os)).1.length = pathCalls os := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [checkAll, eval_bind, eval, List.append_nil, List.length_append,
      pathCalls, List.map_cons, List.sum_cons]
    rw [check_queries, ih]
    rfl

theorem readFrames_length (frames : List Bytes) (H : Bytes → State) :
    (eval H (readFrames frames)).1.length = frames.length := by
  induction frames with
  | nil => rfl
  | cons a rest ih =>
    simp only [readFrames, eval, List.length_cons, ih]

theorem terminal_length (os : List Opening) (frames : List Bytes) (H : Bytes → State) :
    (eval H (terminal os frames)).1.length = frames.length + pathCalls os := by
  simp only [terminal, eval_bind, List.length_append, readFrames_length, checkAll_length]

theorem pathCalls_uniform (os : List Opening) (depth : Nat)
    (hdepth : ∀ o ∈ os, o.slots.length = depth) :
    pathCalls os = os.length * (depth + 1) := by
  induction os with
  | nil => simp [pathCalls]
  | cons o os ih =>
    have ho := hdepth o (by simp)
    have ht := ih (fun x hx => hdepth x (by simp [hx]))
    simp only [pathCalls, List.map_cons, List.sum_cons, List.length_cons] at *
    rw [ho, ht]
    rw [Nat.add_mul]
    simp [Nat.add_comm]

theorem verifier_budget (D : LiteralByteProtocol.Decoder) (os : List Opening)
    (frames : List Bytes) (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) (queries depth : Nat)
    (hcount : os.length = 3 * queries) (hdepth : ∀ o ∈ os, o.slots.length = depth) :
    (eval H (verifier D (decision os frames) pub pf)).1.length ≤ B_V queries depth frames.length := by
  have ht := terminal_length os frames H
  rw [pathCalls_uniform os depth hdepth, hcount] at ht
  unfold B_V
  rw [Nat.add_assoc]
  exact OracleDecisionPrereqSampler.verifier_length D (decision os frames) H pub pf
    (3 * queries * (depth + 1) + frames.length) (by
      change (eval H (terminal os frames)).1.length ≤ _
      omega)

theorem independent_path_constant : B_V 22 18 6 = 1375 ∧ ¬ B_V 22 18 6 ≤ 1161 := by
  norm_num [B_V]

theorem original_budget (D : LiteralByteProtocol.Decoder) (os : List Opening)
    (frames : List Bytes) (P : RawCutProverCompiler.Prover) (H : Bytes → State)
    (Q queries depth : Nat) (hq : (eval H P).1.length ≤ Q)
    (hcount : os.length = 3 * queries) (hdepth : ∀ o ∈ os, o.slots.length = depth) :
    firstReads emptyTable (eval H (original D (decision os frames) P)).1 ≤
      Q + B_V queries depth frames.length := by
  unfold original
  rw [RawCutProverCompiler.experiment_eval]
  have hv := verifier_budget D os frames H (eval H P).2.1 (eval H P).2.2 queries depth hcount hdepth
  have hr := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (verifier D (decision os frames) (eval H P).2.1 (eval H P).2.2)).1)
  rw [List.length_append] at hr
  dsimp only
  omega

/-- Exact terminal count, with no assumptions on root success or distinctness. -/
theorem frozen_terminal_count (os : List Opening) (frames : List Bytes) (H : Bytes → State)
    (hcount : os.length = 66) (hdepth : ∀ o ∈ os, o.slots.length = 18)
    (hframes : frames.length = 6) :
    (eval H (terminal os frames)).1.length = 1260 := by
  rw [terminal_length, pathCalls_uniform os 18 hdepth, hcount, hframes]

#print axioms checkAll_length
#print axioms readFrames_length
#print axioms terminal_length
#print axioms pathCalls_uniform
#print axioms verifier_budget
#print axioms independent_path_constant
#print axioms original_budget
#print axioms frozen_terminal_count
end AspisR1.OracleDecisionPrereqPaths
end
