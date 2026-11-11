import AspisRec40FollowStatement

/-! Helper lemmas for the follow of rows 33 to 39: list shapes of the actual
context's later rows, `laterRows` over a range, and the challenge of a plain
row of R1's unified run. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FollowLists
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

theorem zip_map_same {α β γ : Type} (l : List α) (f : α → β) (g : α → γ) :
    (l.map f).zip (l.map g) = l.map (fun x => (f x, g x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem range_succ_shift {α : Type} (f : Nat → α) (m : Nat) :
    f 0 :: (List.range m).map (fun j => f (j + 1)) = (List.range (m + 1)).map f := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem range_succ_last {α : Type} (f : Nat → α) (m : Nat) :
    (List.range m).map f ++ [f m] = (List.range (m + 1)).map f := by
  rw [List.range_succ, List.map_append, List.map_singleton]

/-- `laterRows` over consecutive rows. -/
theorem laterRows_range (σ : Nat → State → Cv) (ans : Addr L → State)
    (g : Nat → M × Addr L × State) :
    ∀ (m s : Nat), AspisRows40.Final.laterRows σ ans s ((List.range m).map (fun j => g (s + j))) =
      (List.range m).map (fun j => ((g (s + j)).1, (σ (s + j) (ans (g (s + j)).2.1), (g (s + j)).2.2))) := by
  intro m
  induction m with
  | zero => intro s; rfl
  | succ m ih =>
      intro s
      rw [← range_succ_shift (fun j => g (s + j)) m, ← range_succ_shift
        (fun j => ((g (s + j)).1, (σ (s + j) (ans (g (s + j)).2.1), (g (s + j)).2.2))) m]
      have hs : (fun j => g (s + (j + 1))) = (fun j => g ((s + 1) + j)) := by
        funext j; rw [show s + (j + 1) = s + 1 + j by omega]
      have hs' : (fun j => ((g (s + (j + 1))).1, (σ (s + (j + 1)) (ans (g (s + (j + 1))).2.1),
          (g (s + (j + 1))).2.2))) =
          (fun j => ((g ((s + 1) + j)).1, (σ ((s + 1) + j) (ans (g ((s + 1) + j)).2.1),
            (g ((s + 1) + j)).2.2))) := by
        funext j; rw [show s + (j + 1) = s + 1 + j by omega]
      rw [hs, hs']
      obtain ⟨m0, a0, x0⟩ := g (s + 0)
      simp only [Nat.add_zero] at *
      rw [← ih (s + 1)]
      rfl

/-- The challenge of a plain row `i ≥ 32` of R1's unified run. -/
theorem challenge_plain (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
    (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M) (i : Nat) (hi : 32 ≤ i) :
    UnifiedRun.challenge p hD H pub c1 payload i =
      liftChallenge (p.σ i (H (squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload i))),
        H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload i))) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  unfold UnifiedRun.challenge
  change (eval H (UnifiedSampler.samp p hD (j + 1) (UnifiedRun.transcript p hD H pub c1 payload (j + 1))
    (.payload (payload (j + 1)))).toProgram).2 = _
  rw [UnifiedSampler.row_ordinary p hD (j + 1) (by omega) (by omega) (by omega),
    DuplexSamplers.plain_eval, UnifiedSteps.payload_address p hD H pub c1 payload (j + 1) (by omega)]
  rfl

theorem message_payload (c1 : State) (payload : Nat → M) (i : Nat) (hi : 1 ≤ i) :
    UnifiedRun.message c1 payload i = .payload (payload i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rfl

section ctx
variable (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
  (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)

theorem frames_eq (n : Nat) (hlo : 33 ≤ n) :
    AspisRows40.Final.frames (AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n) =
      (List.range (n - 32)).map (fun j => UnifiedSteps.address p hD H pub c1 payload (32 + j)) := by
  unfold AspisRows40.Final.frames AspisRec40.FollowStatement.actualCtx
  dsimp only
  rw [List.map_map, show n - 32 = (n - 33) + 1 by omega]
  rw [← range_succ_shift (fun j => UnifiedSteps.address p hD H pub c1 payload (32 + j))]
  rw [Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem messages_eq (n : Nat) (hlo : 33 ≤ n) :
    AspisRows40.Final.messages (AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n) =
      (List.range (n - 32)).map (fun j => payload (32 + j)) := by
  unfold AspisRows40.Final.messages AspisRec40.FollowStatement.actualCtx
    AspisRec40.FollowStatement.jointCtx
  dsimp only
  rw [List.map_map, show n - 32 = (n - 33) + 1 by omega]
  rw [← range_succ_shift (fun j => payload (32 + j))]
  rw [Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem frameState_address (i : Nat) :
    AspisRows40.Final.frameState (UnifiedSteps.address p hD H pub c1 payload i) =
      UnifiedRecords.previous p hD H pub c1 payload i := by
  unfold AspisRows40.Final.frameState UnifiedSteps.address
  rw [parseAbsorb_absorbA]
  rfl

theorem nexts_eq (n : Nat) (hlo : 33 ≤ n) :
    AspisRows40.Final.nexts (AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n) =
      (List.range (n - 32)).map (fun j => UnifiedRecords.previous p hD H pub c1 payload (32 + j + 1)) := by
  unfold AspisRows40.Final.nexts AspisRec40.FollowStatement.actualCtx
  dsimp only
  rw [List.map_map, show n - 32 = (n - 33) + 1 by omega,
    ← range_succ_last (fun j => UnifiedRecords.previous p hD H pub c1 payload (32 + j + 1))]
  congr 1
  · apply List.map_congr_left
    intro j _
    simp only [Function.comp, frameState_address]
    rw [show 33 + j = 32 + j + 1 by omega]
  · rw [show 32 + (n - 33) + 1 = n by omega]

end ctx

#print axioms zip_map_same
#print axioms laterRows_range
#print axioms challenge_plain
#print axioms message_payload
#print axioms frames_eq
#print axioms messages_eq
#print axioms frameState_address
#print axioms nexts_eq

end AspisRec40.FollowLists
end
