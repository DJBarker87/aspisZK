import R0P.MaskDuplexDensity

/-! Generic chain and trace-order bookkeeping, independent of the round count. -/
set_option autoImplicit false
namespace R0P.MaskDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P R0P.SemSource R0P.SemD3Glue R0P.Mask
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
section Chain
variable {SM : Type} {L : Nat} (p : Duplex.Params (CM SM) (R0C.SemStatement.Chal SemE SemE) L)
variable (H : Addr L → State)

/-- The chain state after `k` advances. -/
def st (s : State) : Nat → State
  | 0 => s
  | k + 1 => H (advanceA p (st s k))

theorem st_succ' (s : State) : ∀ k, st p H s (k + 1) = st p H (H (advanceA p s)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [st] at ih ⊢; rw [ih]

/-- Events of the completing sampler's chain part. -/
theorem evs_combinedChainBS_mem : ∀ (n : Nat) (s : State) (xs : List State) (e : Bool × Addr L),
    e ∈ evs H (combinedChainBS p n s xs) →
      ∃ k < n, e = (false, squeezeA p (st p H s k)) ∨ e = (true, advanceA p (st p H s k)) := by
  intro n
  induction n with
  | zero => intro s xs e h; simp [combinedChainBS, evs] at h
  | succ n ih =>
      intro s xs e h
      simp only [combinedChainBS, evs, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact ⟨0, by omega, Or.inl rfl⟩
      · exact ⟨0, by omega, Or.inr rfl⟩
      · obtain ⟨k, hk, he⟩ := ih _ _ e h
        refine ⟨k + 1, by omega, ?_⟩
        rw [st_succ']
        exact he

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun k => f (k + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem runOut_combinedChainBS : ∀ (n : Nat) (s : State) (xs : List State),
    runOut H (combinedChainBS p n s xs) =
      (xs ++ (List.range n).map (fun k => st p H s (k + 1)),
        (List.range n).map (fun k => squeezeA p (st p H s k))) := by
  intro n
  induction n with
  | zero => intro s xs; simp [combinedChainBS, runOut]
  | succ n ih =>
      intro s xs
      have e : runOut H (combinedChainBS p (n + 1) s xs) =
          ((runOut H (combinedChainBS p n (H (advanceA p s)) (xs ++ [H (advanceA p s)]))).1,
            squeezeA p s :: (runOut H (combinedChainBS p n (H (advanceA p s)) (xs ++ [H (advanceA p s)]))).2) := rfl
      rw [e, ih, map_range_succ, map_range_succ]
      simp only [List.append_assoc, List.singleton_append, st_succ']
      rfl

/-- The transcript program of the chain reads every chain cell. -/
theorem combinedChainS_reads {C : Type} (out : List State → List State → C) :
    ∀ (n : Nat) (s : State) (bs xs : List State) (k : Nat), k < n →
      squeezeA p (st p H s k) ∈ (eval H (combinedChainS p out n s bs xs).toProgram).1.map Prod.fst ∧
      advanceA p (st p H s k) ∈ (eval H (combinedChainS p out n s bs xs).toProgram).1.map Prod.fst := by
  intro n
  induction n with
  | zero => intro s bs xs k hk; omega
  | succ n ih =>
      intro s bs xs k hk
      simp only [combinedChainS, FS2.Sampler.toProgram, eval, List.map_cons, List.mem_cons]
      cases k with
      | zero => exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
      | succ k =>
          obtain ⟨h1, h2⟩ := ih (H (advanceA p s)) _ _ k (by omega)
          rw [st_succ']
          exact ⟨Or.inr (Or.inr h1), Or.inr (Or.inr h2)⟩

theorem combinedChainS_out {C : Type} (out : List State → List State → C) :
    ∀ (n : Nat) (s : State) (bs xs : List State),
      (eval H (combinedChainS p out n s bs xs).toProgram).2 =
        out (bs ++ (List.range n).map (fun k => H (squeezeA p (st p H s k))))
          (xs ++ (List.range n).map (fun k => st p H s (k + 1))) := by
  intro n
  induction n with
  | zero => intro s bs xs; simp [combinedChainS, FS2.Sampler.toProgram, eval]
  | succ n ih =>
      intro s bs xs
      have e : (eval H (combinedChainS p out (n + 1) s bs xs).toProgram).2 =
          (eval H (combinedChainS p out n (H (advanceA p s)) (bs ++ [H (squeezeA p s)])
            (xs ++ [H (advanceA p s)])).toProgram).2 := rfl
      rw [e, ih, map_range_succ, map_range_succ]
      simp only [List.append_assoc, List.singleton_append, st_succ']
      rfl

/-! ## Trace order inside `traceFrom` -/

section TF
variable {I A : Type} [DecidableEq I]

theorem read_traceFrom (a c : I) : ∀ tr : List (I × A), Read tr a → Read tr c →
    (c = a ∨ Before tr a c) → Read (traceFrom tr a) c := by
  intro tr
  induction tr with
  | nil => intro h; simp [Read] at h
  | cons q rest ih =>
      intro ha hcr hc
      obtain ⟨i, b⟩ := q
      by_cases hia : i = a
      · subst hia
        simp only [traceFrom, if_true]
        exact hcr
      · simp only [traceFrom, hia, if_false]
        have ha' := read_tail i b rest a ha (Ne.symm hia)
        have hci : c ≠ i := by
          rcases hc with rfl | hB
          · exact Ne.symm hia
          · rintro rfl
            have := hB.2
            rw [firstIdx_head] at this
            omega
        apply ih ha' (read_tail i b rest c hcr hci)
        rcases hc with rfl | hB
        · exact Or.inl rfl
        · exact Or.inr (before_tail i b rest a c hB (Ne.symm hia))

theorem before_traceFrom (a c e : I) : ∀ tr : List (I × A), Read tr a →
    (c = a ∨ Before tr a c) → Before tr c e → Before (traceFrom tr a) c e := by
  intro tr
  induction tr with
  | nil => intro h; simp [Read] at h
  | cons q rest ih =>
      intro ha hc hce
      obtain ⟨i, b⟩ := q
      by_cases hia : i = a
      · subst hia
        simp only [traceFrom, if_true]
        exact hce
      · simp only [traceFrom, hia, if_false]
        have ha' := read_tail i b rest a ha (Ne.symm hia)
        have hci : c ≠ i := by
          rcases hc with rfl | hB
          · exact Ne.symm hia
          · rintro rfl
            have := hB.2
            rw [firstIdx_head] at this
            omega
        apply ih ha'
        · rcases hc with rfl | hB
          · exact Or.inl rfl
          · exact Or.inr (before_tail i b rest a c hB (Ne.symm hia))
        · exact before_tail i b rest c e hce hci

end TF

end Chain
#print axioms st_succ'
#print axioms evs_combinedChainBS_mem
#print axioms runOut_combinedChainBS
#print axioms combinedChainS_reads
#print axioms combinedChainS_out
#print axioms read_traceFrom
#print axioms before_traceFrom
end
end R0P.MaskDuplex
