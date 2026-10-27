import R0Z.Shift
import R0Z.TerminalEligible

/-! T2b-1: honest round identities and the terminal-zero chain submodule.
This proves only membership of the remainder, not a mask-image inclusion. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.Chain
open R0P R0P.SemSource R0P.SemDegree R0P.Sumcheck R0Z.MaskLayout
  R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.Shift R0Z.TerminalEligible Polynomial
attribute [local instance] Classical.propDecidable
variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-- Leading Boolean coordinate and tail; no cube is enumerated. -/
def boolConsEquiv (n : Nat) : (Bool × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun b := (b 0, Fin.tail b)
  left_inv p := by cases p; simp only [Fin.cons_zero, Fin.tail_cons]
  right_inv b := Fin.cons_self_tail b

theorem bsumB_eq_sum (n : Nat) (f : (Fin n → Bool) → K) : bsumB n f = ∑ b, f b := by
  induction n with
  | zero =>
    rw [bsumB, Fintype.sum_unique]
    congr 1
  | succ n ih =>
    rw [bsumB, ih, ih]
    have he : (∑ b : Fin (n+1) → Bool, f b) =
        ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) := by
      exact (Fintype.sum_equiv (boolConsEquiv n)
        (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
    rw [he, Fintype.sum_prod_type, Fintype.sum_bool]
    exact add_comm _ _

theorem sum_cons_cast (n m : Nat) (h : n = m+1) (f : (Fin n → Bool) → K) :
    (∑ b, f b) =
      (∑ b : Fin m → Bool, f (fun i => Fin.cons (n := m) (α := fun _ => Bool) false b (Fin.cast h i))) +
      ∑ b : Fin m → Bool, f (fun i => Fin.cons (n := m) (α := fun _ => Bool) true b (Fin.cast h i)) := by
  subst n
  rw [← bsumB_eq_sum, bsumB, bsumB_eq_sum, bsumB_eq_sum]
  rfl

theorem roundPoint_zero (ch : Challenges K) (z : K) (tail : Fin 9 → Bool) :
    roundPoint ch 0 z tail = Fin.cons z (ofBool tail) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [roundPoint, Fin.val_zero, Nat.lt_irrefl, ↓reduceDIte, Fin.cons_zero]
  · simp only [roundPoint, Fin.val_succ, Fin.val_zero, Nat.not_lt_zero, Nat.add_one_ne_zero,
      ↓reduceDIte, Nat.sub_zero, Nat.add_sub_cancel, Fin.cons_succ, ofBool]

theorem roundPoint_cons (ch : Challenges K) (j : Fin 9) (b : Bool)
    (tail : Fin (9-j.succ.val) → Bool) :
    roundPoint ch j.castSucc (alpha ch j.castSucc)
      (fun i => Fin.cons (n := 9-j.succ.val) (α := fun _ => Bool) b tail (Fin.cast (by simp only [Fin.val_castSucc, Fin.val_succ]; omega) i)) =
    roundPoint ch j.succ (if b then 1 else 0) tail := by
  funext i
  have hj : j.castSucc.val = j.val := rfl
  have hj' : j.succ.val = j.val+1 := rfl
  by_cases hlo : i.val < j.val
  · simp only [roundPoint, Fin.val_castSucc, Fin.val_succ, dif_pos hlo,
      dif_pos (show i.val < j.val+1 by omega)]
  · by_cases he : i.val = j.val
    · have hij : i = j.castSucc := Fin.ext he
      subst i
      simp only [roundPoint, Fin.val_castSucc, Fin.val_succ, Nat.lt_irrefl,
        ↓reduceDIte, Nat.lt_succ_self]
    · by_cases hn : i.val = j.val+1
      · simp only [roundPoint, Fin.val_castSucc, Fin.val_succ, dif_neg hlo, dif_neg he,
          dif_neg (show ¬i.val < j.val+1 by omega), dif_pos hn]
        have hz : (Fin.cast (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
            (⟨i.val-j.val-1, by omega⟩ : Fin (9-j.castSucc.val)) : Fin ((9-j.succ.val)+1)) = 0 := by
          apply Fin.ext; simp only [Fin.val_cast, Fin.val_zero, Fin.val_succ, Fin.val_mk]; omega
        exact congrArg (fun x : Bool => if x then (1 : K) else 0)
          ((congrArg (Fin.cons (α := fun _ => Bool) b tail) hz).trans (Fin.cons_zero _ _))
      · have hgt : j.val+1 < i.val := by omega
        simp only [roundPoint, Fin.val_castSucc, Fin.val_succ, dif_neg hlo, dif_neg he,
          dif_neg (show ¬i.val < j.val+1 by omega), dif_neg hn]
        have hs : (Fin.cast (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
            (⟨i.val-j.val-1, by omega⟩ : Fin (9-j.castSucc.val)) : Fin ((9-j.succ.val)+1)) =
            (⟨i.val-(j.val+1)-1, by simp only [Fin.val_succ]; omega⟩ : Fin (9-j.succ.val)).succ := by
          apply Fin.ext; simp only [Fin.val_cast, Fin.val_zero, Fin.val_succ, Fin.val_mk]; omega
        exact congrArg (fun x : Bool => if x then (1 : K) else 0)
          ((congrArg (Fin.cons (α := fun _ => Bool) b tail) hs).trans (Fin.cons_succ _ _ _))

/-- Lemma B, with its T2b-1′ Boolean-domain composition. -/
theorem rounds_initial (ch : Challenges K) (f : PayloadSplit.PointFunction K)
    (hf : VDeg 10 (fun _ => 27) f) :
    (PayloadSplit.rounds ch 0 f).eval 0 + (PayloadSplit.rounds ch 0 f).eval 1 =
      bsumB 10 (fun b => f (ofBool b)) := by
  rw [rounds_eval_of_vdeg ch 0 f hf, rounds_eval_of_vdeg ch 0 f hf]
  change (∑ tail : Fin 9 → Bool, f (roundPoint ch 0 0 tail)) +
    (∑ tail : Fin 9 → Bool, f (roundPoint ch 0 1 tail)) = _
  simp only [roundPoint_zero]
  rw [bsumB, bsumB_eq_sum, bsumB_eq_sum]
  simp only [ofBool_cons, Bool.false_eq_true, ↓reduceIte]

theorem rounds_chain (ch : Challenges K) (f : PayloadSplit.PointFunction K)
    (hf : VDeg 10 (fun _ => 27) f) (j : Fin 9) :
    (PayloadSplit.rounds ch j.succ f).eval 0 + (PayloadSplit.rounds ch j.succ f).eval 1 =
      (PayloadSplit.rounds ch j.castSucc f).eval (alpha ch j.castSucc) := by
  rw [rounds_eval_of_vdeg ch j.succ f hf, rounds_eval_of_vdeg ch j.succ f hf,
    rounds_eval_of_vdeg ch j.castSucc f hf]
  rw [sum_cons_cast (9-j.castSucc.val) (9-j.succ.val)
    (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)]
  simp only [roundPoint_cons, Bool.false_eq_true, ↓reduceIte]

/-! ### The four K-linear constraints -/

/-- Polynomial read from round j's 28 coefficient cells. -/
def roundPoly (j : Fin 10) : Payload K Bat →ₗ[K] K[X] :=
  ∑ i : Fin 28, (monomial i.val).comp (proj (.semanticCoeff j i))

theorem roundPoly_apply (j : Fin 10) (v : Payload K Bat) :
    roundPoly j v = ∑ i : Fin 28, monomial i.val (v (.semanticCoeff j i)) := by
  simp only [roundPoly, LinearMap.sum_apply, LinearMap.comp_apply, proj_apply]

theorem roundPoly_nine : roundPoly (K := K) (Bat := Bat) 9 = round9Poly := rfl

def evalRound (j : Fin 10) (z : K) : Payload K Bat →ₗ[K] K := (Polynomial.leval z).comp (roundPoly j)

theorem evalRound_apply (j : Fin 10) (z : K) (v : Payload K Bat) :
    evalRound j z v = (roundPoly j v).eval z := rfl

/-- The existing nonround projection over K, before restriction to F. -/
def nonRoundK : Payload K Bat →ₗ[K] Payload K Bat :=
  LinearMap.pi fun coord => match coord with
  | .semanticCoeff _ _ => 0
  | coord => (LinearMap.proj coord : Payload K Bat →ₗ[K] K)

theorem nonRoundK_apply (v : Payload K Bat) : nonRoundK v = nonRound (F := F) v := by
  funext coord
  cases coord <;> rfl

/-- Round-only, initial-zero and boundary-chain constraints, before the
terminal value is imposed. This auxiliary space contains `dir`. -/
def InitialChain0 (ch : Challenges K) : Submodule K (Payload K Bat) :=
  (LinearMap.ker nonRoundK ⊓ LinearMap.ker (evalRound 0 0 + evalRound 0 1)) ⊓
    ⨅ j : Fin 9, LinearMap.ker
      (evalRound j.succ 0 + evalRound j.succ 1 - evalRound j.castSucc (alpha ch j.castSucc))

/-- The chain space is a K-submodule: all four conditions are kernels of
K-linear maps. Its explicit membership statement is `mem_chain0_iff`. -/
def Chain0 (ch : Challenges K) : Submodule K (Payload K Bat) :=
  InitialChain0 ch ⊓ LinearMap.ker (evalRound 9 (alpha ch 9))

theorem mem_initialChain0_iff (ch : Challenges K) (v : Payload K Bat) :
    v ∈ InitialChain0 ch ↔ nonRound (F := F) v = 0 ∧
      (roundPoly 0 v).eval 0 + (roundPoly 0 v).eval 1 = 0 ∧
      ∀ j : Fin 9, (roundPoly j.succ v).eval 0 + (roundPoly j.succ v).eval 1 =
        (roundPoly j.castSucc v).eval (alpha ch j.castSucc) := by
  simp only [InitialChain0, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.add_apply, LinearMap.sub_apply, evalRound_apply, nonRoundK_apply (F := F), sub_eq_zero]
  tauto

theorem mem_chain0_iff (ch : Challenges K) (v : Payload K Bat) :
    v ∈ Chain0 ch ↔ nonRound (F := F) v = 0 ∧
      (roundPoly 0 v).eval 0 + (roundPoly 0 v).eval 1 = 0 ∧
      (∀ j : Fin 9, (roundPoly j.succ v).eval 0 + (roundPoly j.succ v).eval 1 =
        (roundPoly j.castSucc v).eval (alpha ch j.castSucc)) ∧
      (roundPoly 9 v).eval (alpha ch 9) = 0 := by
  simp only [Chain0, Submodule.mem_inf, mem_initialChain0_iff (F := F), LinearMap.mem_ker,
    evalRound_apply]
  tauto

theorem roundPoly_roundInclusion (j : Fin 10) (p : PayloadSplit.RoundPayload K) :
    roundPoly j (PayloadSplit.roundInclusion (Bat := Bat) p) = ∑ i : Fin 28, monomial i.val (p j i) := by
  rw [roundPoly_apply]
  rfl

theorem roundPoly_rounds (ch : Challenges K) (j : Fin 10) (f : PayloadSplit.PointFunction K) :
    roundPoly j (PayloadSplit.roundInclusion (Bat := Bat) (fun k i => (PayloadSplit.rounds ch k f).coeff i.val)) =
      PayloadSplit.rounds ch j f := by
  rw [roundPoly_roundInclusion]
  exact sum_monomial_coeff _ (rounds_natDegree_lt ch j f)

theorem roundPoly_originalRounds (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) (j : Fin 10) :
    roundPoly j (PayloadSplit.roundInclusion (Bat := Bat) (PayloadSplit.originalRounds pub B ch t)) =
      PayloadSplit.rounds ch j (fOrig pub B ch t) := by
  rw [originalRounds_eq, roundPoly_rounds]

theorem roundPoly_dir (j : Fin 10) :
    roundPoly j (dir : Payload K Bat) = if j = 9 then X - C (1/2 : K) else 0 := by
  unfold dir
  rw [roundPoly_roundInclusion]
  by_cases hj : j = 9
  · simp only [if_pos hj]
    exact sum_monomial_coeff _ (by rw [natDegree_X_sub_C]; norm_num)
  · simp only [if_neg hj, map_zero, Finset.sum_const_zero]

theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have he : (⟨2, by omega⟩ : Fin 28) = ⟨0, by omega⟩ :=
    nodes_injOn (K := K) (by simp) (by simp)
      (by simpa only [Fin.val_mk, Nat.cast_ofNat, Nat.cast_zero] using h)
  have hv := congrArg Fin.val he
  norm_num at hv

theorem dir_mem_initialChain0 (ch : Challenges K) : (dir : Payload K Bat) ∈ InitialChain0 ch := by
  rw [mem_initialChain0_iff (F := (⊥ : Subfield K))]
  refine ⟨nonRound_dir, ?_, ?_⟩
  · simp only [roundPoly_dir, show (0 : Fin 10) ≠ 9 from by decide, if_false,
      eval_zero, add_zero]
  · intro j
    have hj : j.castSucc ≠ (9 : Fin 10) := by
      intro h
      have he := congrArg Fin.val h
      change j.val = 9 at he
      omega
    rw [roundPoly_dir, roundPoly_dir, if_neg hj, eval_zero]
    by_cases hn : j.succ = (9 : Fin 10)
    · rw [if_pos hn]
      simp only [eval_sub, eval_X, eval_C]
      field_simp [two_ne_zero (K := K)] <;> ring
    · rw [if_neg hn, eval_zero, eval_zero, add_zero]


/-! ### Initial sum and remainder membership -/

/-- Eligible C1 noise leaves every prepared terminal row fixed. Affine H1
padding contributes only the balanced term from Lemma C, whose sum is zero.
The eta factor occurs once, inside `fOrig`. -/
theorem original_bsum_actual (pub : Public K) (B : PackBasis F) (t : Trace K)
    (ch : Challenges K) (r : T K F) :
    bsumB 10 (fun b => fOrig pub B ch (PayloadSplit.actual pub B t ch r) (ofBool b)) =
      bsumB 10 (fun b => fOrig pub B ch (prepare pub t ch) (ofBool b)) := by
  have he (b : Fin 10 → Bool) :
      fOrig pub B ch (PayloadSplit.actual pub B t ch r) (ofBool b) =
      fOrig pub B ch (prepare pub t ch) (ofBool b) +
        (ch.sem 14 * (ch.sem 13 + ch.sem 13 ^ 2)) *
          h1Padding B (Sum.elim 0 (aff r)) (rowOf b) := by
    unfold fOrig PayloadSplit.actual
    rw [terminal_applyAff, terminal_row_eligible]
    ring
  simp_rw [he]
  rw [bsumB_add, bsumB_smul, h1Padding_bsumB, mul_zero, add_zero]

theorem roundPoly_g (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (n : N K F) (j : Fin 10) :
    roundPoly j (roundInclusion (F := F) (Bat := Bat) (g h B x w ch n)) =
      PayloadSplit.rounds ch j (fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch (0,n))) -
      PayloadSplit.rounds ch j (fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0)) := by
  have hg : roundInclusion (F := F) (Bat := Bat) (g h B x w ch n) =
      PayloadSplit.roundInclusion (PayloadSplit.originalRounds x.1 B ch
        (PayloadSplit.actual x.1 B (h.build w) ch (0,n))) -
      PayloadSplit.roundInclusion (PayloadSplit.originalRounds x.1 B ch
        (PayloadSplit.actual x.1 B (h.build w) ch 0)) := map_sub PayloadSplit.roundInclusion _ _
  rw [hg, map_sub, roundPoly_originalRounds, roundPoly_originalRounds]

theorem g_mem_initialChain0 (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (n : N K F) :
    roundInclusion (F := F) (Bat := Bat) (g h B x w ch n) ∈ InitialChain0 ch := by
  rw [mem_initialChain0_iff (F := F)]
  refine ⟨nonRound_roundInclusion _, ?_, ?_⟩
  · rw [roundPoly_g]
    simp only [eval_sub]
    have hn := rounds_initial ch _
      (vdeg_fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch (0,n)))
    have hz := rounds_initial ch _
      (vdeg_fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch (0 : T K F)))
    rw [original_bsum_actual] at hn hz
    linear_combination hn - hz
  · intro j
    rw [roundPoly_g, roundPoly_g]
    simp only [eval_sub]
    have hn := rounds_chain ch _
      (vdeg_fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch (0,n))) j
    have hz := rounds_chain ch _
      (vdeg_fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch (0 : T K F))) j
    linear_combination hn - hz

/-- T2b-1: only the final-coordinate half collision must be excluded.
No mask-image premise, witness-validity premise or stronger Good assumption. -/
theorem sRem_mem_chain0 (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (n : N K F) (hgood : alpha ch 9 ≠ 1/2) :
    sRem (Bat := Bat) h B x w ch n ∈ Chain0 ch := by
  refine ⟨?_, ?_⟩
  · exact (InitialChain0 ch).sub_mem (g_mem_initialChain0 h B x w ch n)
      ((InitialChain0 ch).smul_mem _ (dir_mem_initialChain0 ch))
  · change evalRound9 ch (sRem (Bat := Bat) h B x w ch n) = 0
    have hm : claimMask B (alpha ch) (sRem (Bat := Bat) h B x w ch n) = 0 := by
      unfold sRem
      have hr : claimMask B (alpha ch) (roundInclusion (F := F) (Bat := Bat) (g h B x w ch n)) = 0 := by
        change claimMask B (alpha ch) (PayloadSplit.roundInclusion (Bat := Bat) (g h B x w ch n)) = 0
        exact claimMask_roundInclusion B (alpha ch) _
      rw [map_sub, map_smul, hr, claimMask_dir, smul_zero, sub_zero]
    have hp := Phi0_sRem (Bat := Bat) h B x w ch n hgood
    simpa only [Phi0, LinearMap.sub_apply, hm, sub_zero] using hp

#print axioms sRem_mem_chain0

#print axioms rounds_initial
#print axioms rounds_chain
end R0Z.Chain
