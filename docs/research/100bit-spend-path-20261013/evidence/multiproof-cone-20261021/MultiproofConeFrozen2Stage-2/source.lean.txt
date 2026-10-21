import MultiproofConeBatches

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeFrozen2Stage
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport MultiproofConeVerifyState MultiproofConeBatches
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def sourceBatch (p : Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (batch : Nat) (s : reference.Scratch) : Program Bytes State Bool :=
  bind (sequence p q nodes [(batch,0),(batch,1),(batch,2)] s) (fun out => .done out.1)

/-- The two actual dV_frozen2 batch entry points. The only input refinement
equations identify the fixed physical node slots with their frozen wire views.
No caller lowering or global verifier/annotation join is asserted here. -/
theorem accepted_batch {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (p : Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (batch : Nat) (s : reference.Scratch)
    (views : ∀ k, k<3 → MultiproofConeCanonical.bytesOf (nodes batch k).val=
      slice p.wire (slotStart (3*batch+k)) (32*capacity (3*batch+k)))
    (accepted : (eval H (sourceBatch p q nodes batch s)).2=true) :
    eval H (sourceBatch p q nodes batch s)=
      eval H (OraclePortFrozen2.batch p q [(batch,0),(batch,1),(batch,2)]) := by
  rw [sourceBatch,eval_map] at accepted ⊢
  exact accepted_three D hash H law p q nodes batch s views accepted

/-- TX1 and Pool TX2 use exactly these two triples, with independent initial
scratch and no requirement that either scratch suffix be zero. -/
theorem both_batches {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (p : Parsed) (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → MultiproofConeCanonical.bytesOf (nodes b k).val=
      slice p.wire (slotStart (3*b+k)) (32*capacity (3*b+k))) :
    (∀ s, (eval H (sourceBatch p q nodes 0 s)).2=true →
      eval H (sourceBatch p q nodes 0 s)=eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)) ∧
    (∀ s, (eval H (sourceBatch p q nodes 1 s)).2=true →
      eval H (sourceBatch p q nodes 1 s)=eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)) := by
  constructor
  · intro s accepted
    exact accepted_batch D hash H law p q nodes 0 s (fun k hk => views 0 k (by decide) hk) accepted
  · intro s accepted
    exact accepted_batch D hash H law p q nodes 1 s (fun k hk => views 1 k (by decide) hk) accepted

/-- Outer Bool short-circuit substitution preserves the complete accepted
observation. Arbitrary intervening checkpoint/resume effects stay in place. -/
theorem accepted_outer (H : Bytes → State) (source target continuation : Program Bytes State Bool)
    (join : (eval H source).2=true → eval H source=eval H target)
    (accepted : (eval H (bind source (fun ok => if ok then continuation else .done false))).2=true) :
    eval H (bind source (fun ok => if ok then continuation else .done false))=
      eval H (bind target (fun ok => if ok then continuation else .done false)) := by
  cases result : (eval H source).2 with
  | false => simp only [eval_bind,result,Bool.false_eq_true,if_false,eval] at accepted
  | true => simp only [eval_bind,join result]

#print axioms accepted_batch
#print axioms both_batches
#print axioms accepted_outer
end AspisR1.MultiproofConeFrozen2Stage
end
