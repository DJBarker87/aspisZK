import AspisRec40FollowLists
import R1QueryCompletion

/-! The output prefix of the final component on the actual context of row n
is row n's actual transcript, once the pending answers are the oracle's
(`as = missing.map H`), the table is consistent with the oracle, R1's query
recovery succeeds at the table, and the frames of rows 32 .. n-1 are in the
table with their absorbed states. Algebra only: no trace, no collision. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FollowPrefix
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView
open AspisRows40.Final

variable {M Cv : Type} {L : Nat}

/-- Every squeeze cell of rows 32 .. n-1 absent from the table is pending. -/
theorem squeeze_mem_missing (p : Params M Cv L) (T : Table (Addr L) State)
    (ctx : AspisRows40.Context.Context M L) (b : Addr L) (hb : b ∈ squeezes p T ctx)
    (hnone : T b = none) : b ∈ missing p T ctx := by
  unfold missing
  by_cases hj : b ∈ jointMissing p T ctx
  · exact List.mem_append_left _ hj
  · apply List.mem_append_right
    unfold newMissing
    apply List.mem_dedup.mpr
    apply List.mem_filter.mpr
    refine ⟨hb, ?_⟩
    simp [hnone, hj]

theorem prefix_part (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
    (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (n : Nat) (hlo : 33 ≤ n)
    (T : Table (Addr L) State) (hT : ∀ b v, T b = some v → v = H b)
    (hrec : QueryDecoder.recover p T H (UnifiedQueryRun.queryResult p hD H pub c1 payload).2 =
      some (UnifiedQueryRun.queryAddress p hD H pub c1 payload,
        UnifiedQueryRun.queryResult p hD H pub c1 payload))
    (hcells : ∀ j, j < n - 32 → T (UnifiedSteps.address p hD H pub c1 payload (32 + j)) =
      some (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j))) :
    prefixOf p pub T (AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n)
        ((missing p T (AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n)).map H) =
      UnifiedRun.transcript p hD H pub c1 payload n := by
  generalize hctx : AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n = ctx
  have hjr : ctx.joint.records = UnifiedRecords.records p hD H pub c1 payload 31 := by
    rw [← hctx]; rfl
  have hje : ctx.joint.endpoint = (UnifiedQueryRun.queryResult p hD H pub c1 payload).2 := by
    rw [← hctx]; rfl
  have hjc : ctx.joint.c1 = c1 := by rw [← hctx]; rfl
  have hjq : ctx.joint.queryMessage = payload 31 := by rw [← hctx]; rfl
  -- the joint part of the answers
  have hk : ((missing p T ctx).map H).take (jointMissing p T ctx).length =
      (jointMissing p T ctx).map H := by
    unfold missing
    rw [List.map_append, List.take_left' (by simp)]
  have hjoint : JointPrefixAnswers.fromAnswers p T ctx.joint.records ctx.joint.endpoint
      ((jointMissing p T ctx).map H) =
      (completeRounds p emptyTable H 0 (UnifiedRecords.records p hD H pub c1 payload 31),
        some (UnifiedQueryRun.queryAddress p hD H pub c1 payload,
          UnifiedQueryRun.queryResult p hD H pub c1 payload)) := by
    unfold jointMissing
    rw [JointPrefixAnswers.fromAnswers_map p T _ _ H hT, hjr, hje, hrec]
  -- the answers of the squeeze cells of rows 32 .. n-1
  have hans : ∀ b ∈ squeezes p T ctx,
      (T b).getD (R0C.V3.DQ.accFrom (missing p T ctx) ((missing p T ctx).map H) b) = H b := by
    intro b hb
    exact QueryCompletion.getter_correct T _ H b hT (fun hnone =>
      R0C.V3.DQ.accFrom_map H (missing p T ctx) b (squeeze_mem_missing p T ctx b hb hnone))
  -- the list shapes
  have hsq : squeezes p T ctx = (List.range (n - 32)).map (fun j =>
      squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j))) := by
    unfold squeezes
    rw [← hctx, FollowLists.frames_eq p hD H pub c1 payload n hlo, List.map_map]
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply]
    rw [hcells j (List.mem_range.mp hj)]
    rfl
  have hms : messages ctx = (List.range (n - 32)).map (fun j => payload (32 + j)) := by
    rw [← hctx]; exact FollowLists.messages_eq p hD H pub c1 payload n hlo
  have hns : nexts ctx = (List.range (n - 32)).map
      (fun j => UnifiedRecords.previous p hD H pub c1 payload (32 + j + 1)) := by
    rw [← hctx]; exact FollowLists.nexts_eq p hD H pub c1 payload n hlo
  have hzip : (messages ctx).zip ((squeezes p T ctx).zip (nexts ctx)) =
      (List.range (n - 32)).map (fun j =>
        (fun i => (payload i, squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i),
          UnifiedRecords.previous p hD H pub c1 payload (i + 1))) (32 + j)) := by
    rw [hms, hsq, hns, FollowLists.zip_map_same, FollowLists.zip_map_same]
  -- rounds of the actual transcript
  have hr32 := UnifiedQueryRun.prefix32 p hD H pub c1 payload hl he
  have hrn := UnifiedRun.transcript_rounds p hD H pub c1 payload n
  have hr32' := UnifiedRun.transcript_rounds p hD H pub c1 payload 32
  have hst := UnifiedRun.transcript_statement p hD H pub c1 payload n
  generalize UnifiedRun.transcript p hD H pub c1 payload n = Pn at hrn hst
  generalize hP32 : UnifiedRun.transcript p hD H pub c1 payload 32 = P32 at hr32 hr32'
  obtain ⟨st, rds⟩ := Pn
  simp only at hrn hst
  rw [hst, hrn]
  have hlr : ∀ ans : Addr L → State, laterRows p.σ ans 32 ((List.range (n - 32)).map (fun j =>
      (payload (32 + j), squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j)),
        UnifiedRecords.previous p hD H pub c1 payload (32 + j + 1)))) =
      (List.range (n - 32)).map (fun j => (payload (32 + j),
        (p.σ (32 + j) (ans (squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j)))),
          UnifiedRecords.previous p hD H pub c1 payload (32 + j + 1)))) := fun ans =>
    FollowLists.laterRows_range p.σ ans (fun i => (payload i,
      squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i),
      UnifiedRecords.previous p hD H pub c1 payload (i + 1))) (n - 32) 32
  unfold prefixOf
  simp only [hk, hjoint, hjc, hjq, hzip]
  rw [hlr]
  change (⟨pub, _⟩ : UnifiedSampler.Prefix M Cv L) = ⟨pub, _⟩
  congr 1
  change withQuery c1 _ (payload 31) _ ++ _ = _
  rw [hr32, hr32', show n = 32 + (n - 32) by omega, List.range_add, List.map_append,
    List.map_map, show 32 + (n - 32) - 32 = n - 32 by omega]
  congr 1
  unfold later
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  rw [hans _ (by rw [hsq]; exact List.mem_map.mpr ⟨j, hj, rfl⟩),
    FollowLists.message_payload c1 payload (32 + j) (by omega),
    FollowLists.challenge_plain p hD H pub c1 payload (32 + j) (by omega),
    AspisRec40.FinalRun.final_state_step p hD H pub c1 payload hl he (32 + j) (by omega)]

#print axioms squeeze_mem_missing
#print axioms prefix_part

end AspisRec40.FollowPrefix
end
