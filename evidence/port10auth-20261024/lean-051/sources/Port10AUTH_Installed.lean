import Port10AUTH_Dictionary

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Installed
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

/-- Actual installed physical op5 on either batch, with its complete canonical
read log. Concrete PackedKeys is discharged from query binding. Local parser,
root, node views and callback lowerings stay explicit and source-indexed. -/
theorem accepted {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (p : verifier.Prepared) (folded : Array U8 32#usize) (q : Fin 22 → Fin 262144)
    (binding : Port4B_KeyInstall.queries p.queries=q)
    (batch : Usize) (hb : batch.val<2) (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → bytesOf (nodes b k).val=OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (root0 : Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0))
    (root1 : Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot parsed 1))
    (root2 : folded=encodeState (OraclePortBatchDraft.committedRoot parsed 2))
    (success : Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded batch hash=ok (.Ok ())) :
    eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes batch.val Port4B_BatchJoin.initial)=
      ((eval H (Port9OR_Installed.batch D hash proof p folded batch)).1,true) := by
  let E := Port9OR_Bodies.native D H
  have oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest E) hash H :=
    Port9OR_Code.oracle (VTop_Checkpoint.digest D) hash H
  have keys (k : Fin 3) : Port4B_TreeJoin.PackedKeys Port4B_Install.leaves p.queries q batch
      (Usize.ofNat k.val (by scalar_tac)) :=
    Port4B_KeyInstall.packed Port4B_Install.leaves p.queries q binding batch _ hb (by have:=k.isLt;scalar_tac)
  have joined := Port10AUTH_Batch.accepted Port4B_Install.leaves E hash H oracle occupied sibling leaf
    occupiedGate siblingGate leafGate proof len parsed wire p folded q batch hb nodes views keys root0 root1 root2 success
  have dictionary := Port10AUTH_Dictionary.batch Port4B_Install.leaves (VTop_Checkpoint.digest E)
    (VTop_Checkpoint.digest D) hash proof p folded batch
  have projected : (Port9OR_Code.trace (VTop_Checkpoint.digest E) hash (Port9OR_Installed.code D hash proof p folded batch)).1=
      (Port9OR_Code.trace (VTop_Checkpoint.digest E) hash
        (Port9OR_Batch.code Port4B_Install.leaves (VTop_Checkpoint.digest D) hash proof p folded batch)).1 := by
    exact Port10AUTH_TerminalCut.map_log (VTop_Checkpoint.digest E) hash _
      (fun (out : core.result.Result Unit AspisR1Stage2.verifier.Error) =>
        match out with | .Ok a => .Ok a | .Err e => .Err (Port3_CheckpointInstall.error e))
  have observations := congrArg CheckpointBytes5Inputs.observe
    ((congrArg (fun code => (Port9OR_Code.trace (VTop_Checkpoint.digest E) hash code).1) dictionary).trans projected.symm)
  have effects := congrArg Prod.fst (Port9OR_Installed.effects D hash proof p folded batch H)
  exact joined.trans (congrArg (fun log => (log,true)) (observations.trans effects.symm))

#print axioms accepted
end AspisR1.Port10AUTH_Installed
end
