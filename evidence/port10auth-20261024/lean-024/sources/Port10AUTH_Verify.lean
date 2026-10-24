import Port10AUTH_VerifyCut
import MultiproofConeP6Verify

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Verify
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport MultiproofConePhysicalViews
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Concrete accepted physical verifier transports its complete log and SAME
scratch to the P6 verifier. Only local node lowering, input well-formedness,
alignment/size and per-successful-read oracle interpretation remain. -/
theorem accepted {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (nodeSource : MultiproofConeP6Composition.Node)
    (gate : MultiproofConeP6Composition.NodeGate (rawOracle H) nodeSource)
    (root : Digest) (s out : reference.Scratch) (nodes : Slice U8)
    (well : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst))
    (words : nodes.val.length%32=0) (size : nodes.val.length≤5504)
    (success : erase D hash (Port9OR_P6Verify.code root s nodes)=ok (true,out)) :
    eval H (MultiproofConeP6Verify.verifyState nodeSource root nodes {s with «at»:=0#usize})=
      (CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash (Port9OR_P6Verify.code root s nodes)).1,(true,out)) := by
  obtain ⟨height,rootOK,logs⟩ := Port10AUTH_VerifyCut.accepted D hash root s out nodes success
  have physical := Port10AUTH_Levels.accepted D hash H oracle 18 {s with «at»:=0#usize} nodes (.Done out) height
  have length : ((live s 0 s.n.val).map Prod.fst).length=s.n.val := by
    simp only [List.length_map,MultiproofConeRootGuard.live_length]
  have positive : 0<s.n.val := by
    by_contra bad
    have empty : (live s 0 s.n.val).map Prod.fst=[] := List.length_eq_zero_iff.mp (by omega)
    exact well.1 empty
  have domain : MultiproofConeLevelIteration.Domain nodes {s with «at»:=0#usize} :=
    ⟨positive,by change s.n.val≤16;have bound:=well.2.1;omega,by simp⟩
  have lower := MultiproofConeP6Composition.levels_eq
    (Port9OR_P6Node.digest (Port10AUTH_Total.dictionary D H)) hash (rawOracle H) (fun _ => rfl)
    nodeSource gate nodes size 18 {s with «at»:=0#usize} domain
  have interpreted : eval H (transport (MultiproofConeP6Composition.levels nodeSource 18 {s with «at»:=0#usize} nodes))=
      (CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
        (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)).1,ok (.Done out)) := by
    rw [transport_observation,lower,← physical]
    have value := (Port9OR_Code.trace_value D hash _).trans height
    change ((Port9OR_Code.trace D hash (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)).1.map
      (fun e => (flatten e.1,decodeState e.2)),
      (Port9OR_Code.trace D hash (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)).2)=_
    rw [value]
    rfl
  have guard : OraclePortFrozenOrder.wellFormed
      ((live {s with «at»:=0#usize} 0 s.n.val).map Prod.fst) ∧ nodes.val.length%32=0 := ⟨well,words⟩
  simp only [MultiproofConeP6Verify.verifyState,if_pos guard,eval_bind,interpreted,eval,
    MultiproofConeVerifyState.finishState,rootOK,List.append_nil,logs]

#print axioms accepted
end AspisR1.Port10AUTH_Verify
end
