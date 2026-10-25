import EndP_Collision
set_option autoImplicit false
noncomputable section
namespace AspisR1.EndP_AuthMass
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

/-- Record the SAME source trace without extra queries, then run ALL1040 replay. -/
def program {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :=
  bind (OracleProgramRecording.record source) fun v =>
    bind (SdkC_Replay.replay (project v.2).1 (project v.2).2) fun _ => .done v

def event {A : Type} (v : View Bytes State (View Bytes State A)) : Prop :=
  BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv
    (firstReads emptyTable v.2.1+1040) v

def mass {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) : Rat :=
  lazyMean (program source project) emptyTable (fun v => indicator (event v))

theorem event_mono {A : Type} (v : View Bytes State A) (q r : Nat) (bound : q ≤ r) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv q v →
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv r v := by
  have bad : ∀ a T f,
      AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred q a T f →
      AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred r a T f := by
    rintro a T f ⟨⟨s,card,cover⟩,rest⟩
    exact ⟨⟨s,card.trans_le bound,cover⟩,rest⟩
  have hits : ∀ (tr : List (Bytes × State)) (T : Table Bytes State),
      hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred q) T tr →
      hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred r) T tr := by
    intro tr
    induction tr with
    | nil => intro T h; exact h
    | cons head tail ih =>
      intro T h
      rcases h with ⟨miss,hit⟩ | rest
      · exact Or.inl ⟨miss,bad _ _ _ hit⟩
      · exact Or.inr (ih _ rest)
  exact hits v.1 emptyTable

/-- The observed alternative is literally AuS1_Finish.Collision, rather than
an unrelated event with the same numerical bound. -/
theorem same_alternative {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State) :
    event (eval H (program source project)) ↔
      AuS1_Finish.Collision H (eval H source).1 (project (eval H source).2).1
        (project (eval H source).2).2 := by
  simp only [event,program,OracleProgramRecording.eval_record,eval_bind,eval,
    List.append_nil,BinRawByteCollisionTargets.event,AuS1_Finish.Collision]

/-- No independence or fixed-Q equality is assumed: the actual source first
reads in AuS1's event are enlarged monotonically to the proven global budget. -/
theorem bound {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q+22585) :
    mass source project ≤ EndP_Numeric.authLoss Q := by
  apply (OracleProgramLawExt.lazyMean_le_of_eval (program source project)
    (SdkC_Replay.augmented source project) (fun v => indicator (event v))
    (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv
      (Q+23625) v)) ?_).trans (EndP_Collision.loss source project Q budget)
  intro H
  apply indicator_mono
  intro hit
  have hb : firstReads emptyTable (eval H source).1+1040 ≤ Q+23625 := by
    have h := budget H
    omega
  have sourceLog : (eval H (program source project)).2.1 = (eval H source).1 := by
    simp only [program,OracleProgramRecording.eval_record,eval_bind,eval]
  unfold event at hit
  rw [sourceLog] at hit
  have enlarged := event_mono (eval H (program source project)) _ _ hb hit
  simpa only [program,SdkC_Replay.augmented,OracleProgramRecording.eval_record,
    eval_bind,eval,List.append_nil,BinRawByteCollisionTargets.event] using enlarged

#print axioms event_mono
#print axioms same_alternative
#print axioms bound
end AspisR1.EndP_AuthMass
end
