import F3Q_VerifyGuards
import F3Q_VerifyLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_VerifyAccepted
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConePhysicalViews MultiproofConePhysicalTransport

theorem log {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (rawOracle H parts))
    (occupied sibling : MultiproofConeP6Callbacks.Parent)
    (og : MultiproofConeP6Callbacks.ParentGate (rawOracle H) occupied)
    (sg : MultiproofConeP6Callbacks.ParentGate (rawOracle H) sibling)
    (root : Array U8 32#usize) (s out : reference.Scratch) (nodes : Slice U8)
    (well : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst))
    (words : nodes.val.length%32=0) (size : nodes.val.length≤5504)
    (success : reference.verify_owned (Port9OR_P6Node.digest D) hash root s nodes=ok (true,out)) :
    (eval H (SdkC_Oracle.program (Port9OR_P6Verify.code root s nodes))).1=
      (eval H (MultiproofConeP6Verify.verifyState (MultiproofConeP6Callbacks.nodeWith occupied sibling)
        root nodes {s with «at»:=0#usize})).1 := by
  have wrapper : MultiproofConeP6Verify.wrapper
      (fun t=>reference.levels (Port9OR_P6Node.digest D) hash t nodes 18#u32) root s nodes=ok (true,out) := success
  obtain ⟨nonzero,bounded,valid,multiple⟩ := F3Q_VerifyGuards.accepted _ root s out nodes wrapper
  rw [F3Q_VerifyLog.code_log H root s nodes nonzero bounded valid multiple]
  have positive : 0<s.n.val := by
    by_contra bad
    exact nonzero (UScalar.eq_of_val_eq (by change s.n.val=0;omega))
  have bound : s.n.val≤16 := by change ¬s.n.val>16 at bounded;omega
  have domain : MultiproofConeLevelIteration.Domain nodes {s with «at»:=0#usize} := ⟨positive,bound,by simp⟩
  have lower := F3N_P6LevelLog.callbacks (Port9OR_P6Node.digest D) hash H law occupied sibling og sg
    18 {s with «at»:=0#usize} nodes size domain
  rw [congrArg Prod.fst lower]
  have guard : OraclePortFrozenOrder.wellFormed
      ((live {s with «at»:=0#usize} 0 s.n.val).map Prod.fst) ∧ nodes.val.length%32=0 := ⟨well,words⟩
  simp only [MultiproofConeP6Verify.verifyState,if_pos guard,eval_bind,eval,List.append_nil]

#print axioms log
end AspisR1.F3Q_VerifyAccepted
end
