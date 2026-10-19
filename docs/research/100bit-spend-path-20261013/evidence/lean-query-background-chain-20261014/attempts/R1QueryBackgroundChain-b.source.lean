import R1QuerySampler
import R0C.V3.DQDecodes

/-! Generic structural bookkeeping for a paired squeeze/advance query chain.
Order and state-distinctness remain explicit hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryBackgroundChain

open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def chainBS (p : Params M Cv L) : Nat → State → List State → BS (Addr L) State (List State)
  | 0, _, xs => .done xs
  | n + 1, s, xs => .spawn (squeezeA p s)
      (.ask (advanceA p s) fun x => chainBS p n x (xs ++ [x]))

theorem evs_chainBS_mem (p : Params M Cv L) (H : Addr L → State) :
    ∀ (n : Nat) (s : State) (xs : List State) (e : Bool × Addr L),
      e ∈ evs H (chainBS p n s xs) →
        ∃ k < n,
          e = (false, squeezeA p (QuerySampler.state p H s k)) ∨
          e = (true, advanceA p (QuerySampler.state p H s k)) := by
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
        rw [QuerySampler.state_succ' p H s k]
        exact he

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun k => f (k + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem runOut_chainBS (p : Params M Cv L) (H : Addr L → State) :
    ∀ (n : Nat) (s : State) (xs : List State),
      runOut H (chainBS p n s xs) =
        (xs ++ (List.range n).map (fun k => QuerySampler.state p H s (k + 1)),
          (List.range n).map (fun k => squeezeA p (QuerySampler.state p H s k))) := by
  intro n
  induction n with
  | zero => intro s xs; simp [chainBS, runOut]
  | succ n ih =>
      intro s xs
      let tail := chainBS p n (H (advanceA p s)) (xs ++ [H (advanceA p s)])
      have e : runOut H (chainBS p (n + 1) s xs) =
          ((runOut H tail).1, squeezeA p s :: (runOut H tail).2) := rfl
      rw [e, ih, map_range_succ, map_range_succ]
      simp only [List.append_assoc, List.singleton_append, QuerySampler.state_succ']
      rfl

theorem order_chain (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) :
    ∀ (n : Nat) (s : State) (xs : List State),
      (∀ j k, j < k → k < n →
        Before tr (advanceA p (QuerySampler.state p H s j))
          (squeezeA p (QuerySampler.state p H s k)) ∧
        Before tr (advanceA p (QuerySampler.state p H s j))
          (advanceA p (QuerySampler.state p H s k))) →
      OrderOK tr (evs H (chainBS p n s xs)) := by
  intro n
  induction n with
  | zero => intro s xs _; trivial
  | succ n ih =>
      intro s xs h
      refine ⟨fun hb => absurd hb (by simp), fun _ e he => ?_, ih _ _ ?_⟩
      · obtain ⟨k, hk, he'⟩ := evs_chainBS_mem p H n _ _ e he
        have h' := h 0 (k + 1) (by omega) (by omega)
        rw [QuerySampler.state_succ' p H s k] at h'
        rcases he' with rfl | rfl
        · exact h'.1
        · exact h'.2
      · intro j k hjk hk
        have h' := h (j + 1) (k + 1) (by omega) (by omega)
        rw [QuerySampler.state_succ' p H s j,
          QuerySampler.state_succ' p H s k] at h'
        exact h'

theorem chain_nodup (p : Params M Cv L) (H : Addr L → State) :
    ∀ (n : Nat) (s : State) (xs : List State),
      (∀ j k, j < k → k < n →
        QuerySampler.state p H s j ≠ QuerySampler.state p H s k) →
      ((evs H (chainBS p n s xs)).map Prod.snd).Nodup := by
  intro n
  induction n with
  | zero => intro s xs _; simp [chainBS, evs]
  | succ n ih =>
      intro s xs h
      let tail := chainBS p n (H (advanceA p s)) (xs ++ [H (advanceA p s)])
      have hrest : ∀ c ∈ (evs H tail).map Prod.snd,
          ∃ k < n,
            c = squeezeA p (QuerySampler.state p H s (k + 1)) ∨
            c = advanceA p (QuerySampler.state p H s (k + 1)) := by
        intro c hc
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
        obtain ⟨k, hk, he'⟩ := evs_chainBS_mem p H n _ _ e he
        refine ⟨k, hk, ?_⟩
        rw [QuerySampler.state_succ' p H s k]
        rcases he' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      simp only [chainBS, evs, List.map_cons, List.nodup_cons, List.mem_cons, not_or]
      refine ⟨⟨squeezeA_ne_advanceA' p _ _, fun hm => ?_⟩, fun hm => ?_, ih _ _ ?_⟩
      · obtain ⟨k, hk, hc⟩ := hrest _ hm
        rcases hc with hc | hc
        · exact h 0 (k + 1) (by omega) (by omega) (squeezeA_injective p hc)
        · exact squeezeA_ne_advanceA' p _ _ hc
      · obtain ⟨k, hk, hc⟩ := hrest _ hm
        rcases hc with hc | hc
        · exact squeezeA_ne_advanceA' p _ _ hc.symm
        · exact h 0 (k + 1) (by omega) (by omega) (advanceA_injective p hc)
      · intro j k hjk hk
        have h' := h (j + 1) (k + 1) (by omega) (by omega)
        rwa [QuerySampler.state_succ' p H s j,
          QuerySampler.state_succ' p H s k] at h'

#print axioms evs_chainBS_mem
#print axioms runOut_chainBS
#print axioms order_chain
#print axioms chain_nodup

end AspisR1.QueryBackgroundChain
end
