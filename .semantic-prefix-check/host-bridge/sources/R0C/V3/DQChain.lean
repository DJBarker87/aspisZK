import R0C.V3.DuplexQDensity
import FS2.DuplexDecodes

/-! # Bookkeeping for the q22 duplex chain

`st s k`: the chain state after `k` advances from `s`.  The run of the
completing sampler's chain, its events, the transcript program's reads and
output, and the transfer of trace order to `traceFrom`. -/
set_option autoImplicit false
namespace R0C.V3.DQ

open FS FS2 FS2.Duplex R0FS R0FS.V2 R0C.V3
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

variable {L : Nat} (p : Duplex.Params (Msg E) (R0FS.Chal E) L) (H : Addr L → State)

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
theorem evs_chainBS_mem : ∀ (n : Nat) (s : State) (xs : List State) (e : Bool × Addr L),
    e ∈ evs H (chainBS p n s xs) →
      ∃ k < n, e = (false, squeezeA p (st p H s k)) ∨ e = (true, advanceA p (st p H s k)) := by
  intro n
  induction n with
  | zero => intro s xs e h; simp [chainBS, evs] at h
  | succ n ih =>
      intro s xs e h
      simp only [chainBS, evs, List.mem_cons] at h
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

theorem runOut_chainBS : ∀ (n : Nat) (s : State) (xs : List State),
    runOut H (chainBS p n s xs) =
      (xs ++ (List.range n).map (fun k => st p H s (k + 1)),
        (List.range n).map (fun k => squeezeA p (st p H s k))) := by
  intro n
  induction n with
  | zero => intro s xs; simp [chainBS, runOut]
  | succ n ih =>
      intro s xs
      have e : runOut H (chainBS p (n + 1) s xs) =
          ((runOut H (chainBS p n (H (advanceA p s)) (xs ++ [H (advanceA p s)]))).1,
            squeezeA p s :: (runOut H (chainBS p n (H (advanceA p s)) (xs ++ [H (advanceA p s)]))).2) := rfl
      rw [e, ih, map_range_succ, map_range_succ]
      simp only [List.append_assoc, List.singleton_append, st_succ']
      rfl

/-- The transcript program of the chain reads every chain cell. -/
theorem chainS_reads {C : Type} (out : List State → List State → C) :
    ∀ (n : Nat) (s : State) (bs xs : List State) (k : Nat), k < n →
      squeezeA p (st p H s k) ∈ (eval H (chainS p out n s bs xs).toProgram).1.map Prod.fst ∧
      advanceA p (st p H s k) ∈ (eval H (chainS p out n s bs xs).toProgram).1.map Prod.fst := by
  intro n
  induction n with
  | zero => intro s bs xs k hk; omega
  | succ n ih =>
      intro s bs xs k hk
      simp only [chainS, FS2.Sampler.toProgram, eval, List.map_cons, List.mem_cons]
      cases k with
      | zero => exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
      | succ k =>
          obtain ⟨h1, h2⟩ := ih (H (advanceA p s)) _ _ k (by omega)
          rw [st_succ']
          exact ⟨Or.inr (Or.inr h1), Or.inr (Or.inr h2)⟩

theorem chainS_out {C : Type} (out : List State → List State → C) :
    ∀ (n : Nat) (s : State) (bs xs : List State),
      (eval H (chainS p out n s bs xs).toProgram).2 =
        out (bs ++ (List.range n).map (fun k => H (squeezeA p (st p H s k))))
          (xs ++ (List.range n).map (fun k => st p H s (k + 1))) := by
  intro n
  induction n with
  | zero => intro s bs xs; simp [chainS, FS2.Sampler.toProgram, eval]
  | succ n ih =>
      intro s bs xs
      have e : (eval H (chainS p out (n + 1) s bs xs).toProgram).2 =
          (eval H (chainS p out n (H (advanceA p s)) (bs ++ [H (squeezeA p s)])
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

#print axioms runOut_chainBS
#print axioms chainS_out
#print axioms before_traceFrom
end
end R0C.V3.DQ
