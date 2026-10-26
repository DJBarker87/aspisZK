import RPz7_LogA_Tags
import OraclePortFrozen2Digests
set_option autoImplicit false
noncomputable section
namespace AspisR1.LogA_Dependencies
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4

/-- The headline verifier includes sampler initialization before its decision.
No acceptance premise, no source/model log equality is asserted here. -/
theorem verifier_initial_head (D : LiteralByteProtocol.Decoder)
    (stored : Bytes) (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (root : State) (word : LiteralTranscript.C1Word)
    (first : pf 0 = .initial root word) (H : Bytes → State) :
    (eval H (verifier D OraclePortFrozen2.dV_frozen2
      ⟨pub,pf,stored⟩)).1.head? =
      some (PublicInitFrame.frame pub.pubBytes root,
        H (PublicInitFrame.frame pub.pubBytes root)) := by
  change (eval H (OracleDecisionFeasibilityCore.verifierFrom D _ pf 33
    (emptyPrefix pub))).1.head? = _
  rw [OracleDecisionFeasibilityCore.verifierFrom]
  apply RawK_ModelHead.bind_head
  change (eval H (LiteralByteSampler.samp 0 _ (pf 0)).toProgram).1.head? = _
  rw [first,LiteralByteSampler.eval_eq]
  simp only [LiteralTranscript.samp,LiteralTranscript.erase,UnifiedSampler.samp,
    DuplexSamplers.initial,Sampler.toProgram,eval,mapView,List.map_cons,List.head?_cons,
    PublicInitFrame.addr,Addr.toBytes_ofBytes]
  all_goals rfl

/-- The eight-pair chain's addresses depend on advance answers, not squeeze
answers. Agreement is required on the complete advance domain, including
previously queried addresses; this is not an independent-answer assumption. -/
theorem query_states_agree {M Cv : Type} {L : Nat} (p : Params M Cv L)
    (H G : Addr L → State)
    (sameAdvance : ∀ s, H (advanceA p s) = G (advanceA p s)) (s : State) (n : Nat) :
    QuerySampler.state p H s n = QuerySampler.state p G s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [QuerySampler.state,ih,sameAdvance]

/-- Given the absorbed state, advance's input is already fixed before the
squeeze answer. Extracted directly from the model's actual plain sampler. -/
theorem plain_inputs {M Cv C : Type} {L : Nat} (p : Params M Cv L)
    (a : Addr L) (i : Nat) (f : Chal Cv → C) (H : Addr L → State) :
    ((eval H (DuplexSamplers.plain p a i f).toProgram).1.map Prod.fst) =
      [a,squeezeA p (H a),advanceA p (H a)] := rfl

/-- A leaf's input is determined by parsed bytes and position, not any
answer. Which position is selected still depends on the earlier query sampler. -/
theorem leaf_first (p : OraclePortCompactDraft.Parsed) (kind pos : Nat)
    (H : Bytes → State) :
    (eval H (.ask (OraclePortSelectedDraft.leaf p kind pos)
      (fun d => .done d))).1.head? =
      some (OraclePortSelectedDraft.leaf p kind pos,H (OraclePortSelectedDraft.leaf p kind pos)) := rfl

/-- Checksum INPUT depends on the proof/public digest answers. It is invariant
when those two answers and the prepared/accumulator values are fixed. -/
theorem checksum_input_agree (H G : Bytes → State) (stored pub : Bytes)
    (p : OraclePortCheckpointAbiC5.Prepared)
    (a : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (hp : H stored = G stored) (hu : H pub = G pub) :
    OraclePortPhysicalFrameDraft.domain ++ OraclePortCheckpointAbiC5.body p a (H stored) (H pub) =
      OraclePortPhysicalFrameDraft.domain ++ OraclePortCheckpointAbiC5.body p a (G stored) (G pub) := by
  rw [hp,hu]

#print axioms verifier_initial_head
#print axioms query_states_agree
#print axioms plain_inputs
#print axioms leaf_first
#print axioms checksum_input_agree
end AspisR1.LogA_Dependencies
end
