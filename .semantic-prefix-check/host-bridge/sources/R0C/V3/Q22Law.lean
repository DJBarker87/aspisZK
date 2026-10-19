import R0C.QuerySource
import R0C.QuerySampler

/-! # The q22 round as a full-read chain

`scanOut` is the tree's q22 loop as a function of the squeezed blocks and the
advanced states; `chainE` is the law of `n` independent (squeeze, advance)
pairs.  `chainE_scanOut`: reading all `n` pairs and scanning gives the same
output law as the tree's early-stopping `loopProgram` (the reads after the
stop are averaged out).  `q22_bound`: the successful 22-subset event inside
a set of at most 9557 fibres has mass at most C(9557,22)/C(262144,22);
failure contributes nothing. -/
set_option autoImplicit false
namespace R0C.V3.Q22

open AspisV8R19 AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep SamplerWords
open Q22WordScan Q22SamplerProgram SourceOraclePrograms
open MemoizedProgramLaw OracleProgramOps AdaptiveFirstReadLaw OracleResampling
open CausalFirstHitUnionBound
noncomputable section

def scanOut : Nat → ScanState → List State → List State → State → Result
  | 0, q, _, _, s => (finish q, s)
  | n + 1, q, b :: bs, x :: xs, s =>
      if q.draws < 64 then
        (if (scan q (words 18 b)).2 then (finish (scan q (words 18 b)).1, x)
         else scanOut n (scan q (words 18 b)).1 bs xs x)
      else (finish q, s)
  | _ + 1, q, [], _, s => (finish q, s)
  | _ + 1, q, _ :: _, [], s => (finish q, s)

def chainE (F : List State → List State → ℚ) : Nat → ℚ
  | 0 => F [] []
  | n + 1 => mean (fun b : State => mean (fun x : State => chainE (fun bs xs => F (b :: bs) (x :: xs)) n))

theorem chainE_const (c : ℚ) : ∀ n, chainE (fun _ _ => c) n = c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [chainE, ih]
      rw [mean_congr (fun b => mean_const c), mean_const]

theorem chainE_mono : ∀ (n : Nat) (F G : List State → List State → ℚ),
    (∀ bs xs, F bs xs ≤ G bs xs) → chainE F n ≤ chainE G n := by
  intro n
  induction n with
  | zero => intro F G h; exact h [] []
  | succ n ih =>
      intro F G h
      exact FS.mean_mono fun b => FS.mean_mono fun x => ih _ _ fun bs xs => h _ _

theorem chainE_scanOut : ∀ (n : Nat) (s : State) (q : ScanState) (F : Result → ℚ),
    chainE (fun bs xs => F (scanOut n q bs xs s)) n =
      independentMean (loopProgram n s q) (fun v => F v.2) := by
  intro n
  induction n with
  | zero => intro s q F; rfl
  | succ n ih =>
      intro s q F
      by_cases hd : q.draws < 64
      · simp only [loopProgram, if_pos hd]
        rw [independentMean_bind]
        change mean (fun b : State => mean (fun x : State =>
            chainE (fun bs xs => F (scanOut (n + 1) q (b :: bs) (x :: xs) s)) n)) =
          mean (fun b : State => mean (fun x : State =>
            independentMean
              (if (scan q (words 18 b)).2 then Program.done (finish (scan q (words 18 b)).1, x)
               else loopProgram n x (scan q (words 18 b)).1)
              (fun second => F second.2)))
        apply mean_congr; intro b; apply mean_congr; intro x
        simp only [scanOut, if_pos hd]
        by_cases hs : (scan q (words 18 b)).2 = true
        · simp only [hs, if_true]
          rw [chainE_const]
          rfl
        · simp only [hs, Bool.false_eq_true, if_false]
          exact ih x _ F
      · simp only [loopProgram, if_neg hd]
        change chainE (fun bs xs => F (scanOut (n + 1) q bs xs s)) (n + 1) = F (finish q, s)
        simp only [chainE]
        have hc : ∀ b x : State, chainE (fun bs xs => F (scanOut (n + 1) q (b :: bs) (x :: xs) s)) n =
            F (finish q, s) := by
          intro b x
          simp only [scanOut, if_neg hd]
          exact chainE_const _ n
        rw [mean_congr (fun b => (mean_congr (fun x => hc b x)).trans (mean_const _)), mean_const]

/-- The round-4 query set: the successful result's 22 fibres, or `∅` on
failure (which the verifier rejects). -/
def chalSet : Except Nat (List Nat) → Finset (Fin 262144)
  | .ok xs => (QuerySampler.querySet xs).map ⟨Fin.cast (by norm_num), Fin.cast_injective _⟩
  | .error _ => ∅

def q0 : ScanState := ⟨[], 0⟩

theorem chalSet_event_le (M : Finset (Fin 262144)) (r : Except Nat (List Nat)) :
    indicator ((chalSet r).card = 22 ∧ chalSet r ⊆ M) ≤
      QuerySource.containsOnly (M.map ⟨Fin.cast (by norm_num), Fin.cast_injective _⟩) r := by
  cases r with
  | error n =>
      simp only [chalSet, Finset.card_empty, QuerySource.containsOnly]
      rw [FS.indicator_iff (q := False) (by simp), FS.indicator_false]
  | ok xs =>
      simp only [QuerySource.containsOnly]
      apply FS.indicator_mono
      rintro ⟨_, hsub⟩ x hx
      have hm : (⟨x % (2^18), Nat.mod_lt _ (by positivity)⟩ : Fin (2^18)) ∈ QuerySampler.querySet xs := by
        simp only [QuerySampler.querySet, Finset.mem_image, List.mem_toFinset]
        exact ⟨x, hx, rfl⟩
      have := hsub (Finset.mem_map_of_mem _ hm)
      rw [Finset.mem_map]
      exact ⟨_, this, by ext; simp⟩

/-- Round 4's flip mass for a fixed matching set. -/
theorem q22_bound (s : State) (M : Finset (Fin 262144)) (hM : M.card ≤ 9557) :
    chainE (fun bs xs => indicator ((chalSet (scanOut 8 q0 bs xs s).1).card = 22 ∧
      chalSet (scanOut 8 q0 bs xs s).1 ⊆ M)) 8 ≤
      (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by
  set M' : Finset (Fin (2^18)) := M.map ⟨Fin.cast (by norm_num), Fin.cast_injective _⟩ with hM'
  calc chainE (fun bs xs => indicator ((chalSet (scanOut 8 q0 bs xs s).1).card = 22 ∧
        chalSet (scanOut 8 q0 bs xs s).1 ⊆ M)) 8
      ≤ chainE (fun bs xs => QuerySource.containsOnly M' (scanOut 8 q0 bs xs s).1) 8 :=
        chainE_mono 8 _ _ fun bs xs => chalSet_event_le M _
    _ = independentMean (challengeProgram s) (fun v => QuerySource.containsOnly M' v.2.1) :=
        chainE_scanOut 8 s q0 (fun r => QuerySource.containsOnly M' r.1)
    _ ≤ (M'.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := QuerySource.successful_subset_le s M'
    _ ≤ (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [hM', Finset.card_map]
        exact_mod_cast Nat.choose_le_choose 22 hM

#print axioms chainE_scanOut
#print axioms q22_bound
end
end R0C.V3.Q22
