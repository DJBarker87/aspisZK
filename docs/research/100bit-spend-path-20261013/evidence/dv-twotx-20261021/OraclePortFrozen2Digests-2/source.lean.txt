import OraclePortFrozen2Checkpoint

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozen2Digests
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5 OraclePortCheckpointOracleC5
attribute [local irreducible] OraclePortCheckpointStateC3.write OraclePortCheckpointStateC3.advance
  QueryAccumulator.run QueryAccumulator.run22

theorem writer_log (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) :
    (eval H (writer stored pub p a)).1 =
      [(stored,H stored),(pub,H pub),
       (OraclePortPhysicalFrameDraft.domain ++ body p a (H stored) (H pub),
        H (OraclePortPhysicalFrameDraft.domain ++ body p a (H stored) (H pub)))] := rfl

theorem resumer_log (H : Bytes → State) (pub : Bytes)
    (d : MatchingSupport.Data E) (saved : Carrier) :
    (eval H (resumer pub d saved)).1 =
      [(saved.stored,H saved.stored),(pub,H pub),
       (OraclePortPhysicalFrameDraft.domain ++ saved.checkpoint.take 1736,
        H (OraclePortPhysicalFrameDraft.domain ++ saved.checkpoint.take 1736))] := rfl

/-- The writer and successful reader use the identical domain/body address.
Proof and public digests likewise repeat the same bytes in the same order. -/
theorem saved_body (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    (save H stored pub c d rho q).checkpoint.take 1736 =
      body (prepared c d rho q) (OraclePortCheckpointStateC3.write (model d rho q)).accumulator
        (H stored) (H pub) :=
  (checksum_bound H stored pub (prepared c d rho q)
    (OraclePortCheckpointStateC3.write (model d rho q)).accumulator).1

theorem six_ordered_reads (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    let a := OraclePortPhysicalFrameDraft.domain ++ (save H stored pub c d rho q).checkpoint.take 1736
    (eval H (writeResume stored pub c d rho q)).1 =
      [(stored,H stored),(pub,H pub),(a,H a),
       (stored,H stored),(pub,H pub),(a,H a)] := by
  dsimp only
  simp only [writeResume,eval_bind,writer_value,writer_log,resumer_log]
  simp only [save,(checksum_bound H stored pub (prepared c d rho q)
    (OraclePortCheckpointStateC3.write (model d rho q)).accumulator).1]
  rfl

#print axioms writer_log
#print axioms resumer_log
#print axioms saved_body
#print axioms six_ordered_reads
end AspisR1.OraclePortFrozen2Digests
end
