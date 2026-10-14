import R1QueryFirstRead

/-! A generic paired squeeze/advance sampler and its exact evaluated output
and read set. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QuerySampler

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat} (p : Params M Cv L) (H : Addr L → State)

def state (p : Params M Cv L) (H : Addr L → State) (s : State) : Nat → State
  | 0 => s
  | n + 1 => H (advanceA p (state p H s n))

def chain {C : Type} (p : Params M Cv L)
    (out : List State → List State → C) :
    Nat → State → List State → List State → Sampler (Addr L) State C
  | 0, _, bs, xs => .done (out bs xs)
  | n + 1, s, bs, xs => .ask (squeezeA p s) fun b =>
      .ask (advanceA p s) fun x => chain p out n x (bs ++ [b]) (xs ++ [x])

theorem state_succ' (s : State) : ∀ n,
    state p H s (n + 1) = state p H (H (advanceA p s)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [state] at ih ⊢; rw [ih]

theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun k => f (k + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem chain_out {C : Type} (out : List State → List State → C) :
    ∀ n s bs xs,
      (eval H (chain p out n s bs xs).toProgram).2 =
        out (bs ++ (List.range n).map (fun k => H (squeezeA p (state p H s k))))
          (xs ++ (List.range n).map (fun k => state p H s (k + 1))) := by
  intro n
  induction n with
  | zero => intro s bs xs; simp [chain, Sampler.toProgram, eval]
  | succ n ih =>
      intro s bs xs
      have e : (eval H (chain p out (n + 1) s bs xs).toProgram).2 =
          (eval H (chain p out n (H (advanceA p s))
            (bs ++ [H (squeezeA p s)]) (xs ++ [H (advanceA p s)])).toProgram).2 := rfl
      rw [e, ih, map_range_succ, map_range_succ]
      simp only [List.append_assoc, List.singleton_append, state_succ']
      rfl

theorem chain_reads {C : Type} (out : List State → List State → C) :
    ∀ n s bs xs k, k < n →
      squeezeA p (state p H s k) ∈ (eval H (chain p out n s bs xs).toProgram).1.map Prod.fst ∧
      advanceA p (state p H s k) ∈ (eval H (chain p out n s bs xs).toProgram).1.map Prod.fst := by
  intro n
  induction n with
  | zero => intro s bs xs k hk; omega
  | succ n ih =>
      intro s bs xs k hk
      simp only [chain, Sampler.toProgram, eval, List.map_cons, List.mem_cons]
      cases k with
      | zero => exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
      | succ k =>
          obtain ⟨h1, h2⟩ := ih (H (advanceA p s)) _ _ k (by omega)
          rw [state_succ']
          exact ⟨Or.inr (Or.inr h1), Or.inr (Or.inr h2)⟩

#print axioms state_succ'
#print axioms map_range_succ
#print axioms chain_out
#print axioms chain_reads

end AspisR1.QuerySampler
end
