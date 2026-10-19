import R0P.SemD3
import Mathlib.Order.Interval.Finset.Fin

/-! Coordinate-wise functional degree. The recursive definition mirrors MLDeg
and keeps disjoint high/low selector supports throughout multiplication. -/
set_option autoImplicit false
noncomputable section
namespace R0P.SemDegree
open Polynomial SemBadSets Sumcheck SemSource
variable {K : Type} [Field K]

/-- A separate polynomial degree bound for each source coordinate. -/
def VDeg : (n : Nat) → (Fin n → Nat) → ((Fin n → K) → K) → Prop
  | 0, _, _ => True
  | n+1, d, G => (∀ x, VDeg n (Fin.tail d) (fun v => G (Fin.cons x v))) ∧
      ∀ v, ∃ p : K[X], p.natDegree ≤ d 0 ∧ ∀ x, p.eval x = G (Fin.cons x v)

#print axioms VDeg

theorem vdeg_const (n : Nat) (d : Fin n → Nat) (c : K) : VDeg n d (fun _ => c) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun _ => ih _, fun _ => ⟨C c, ?_, fun _ => eval_C⟩⟩
      simp only [natDegree_C, Nat.zero_le]

#print axioms vdeg_const

theorem vdeg_mono {n : Nat} {d e : Fin n → Nat} {G : (Fin n → K) → K}
    (h : VDeg n d G) (hde : ∀ i, d i ≤ e i) : VDeg n e G := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun x => ih (h.1 x) (fun i => hde i.succ), ?_⟩
      intro v
      obtain ⟨p, hp, he⟩ := h.2 v
      exact ⟨p, hp.trans (hde 0), he⟩

#print axioms vdeg_mono

theorem vdeg_add {n : Nat} {d e : Fin n → Nat} {G H : (Fin n → K) → K}
    (hG : VDeg n d G) (hH : VDeg n e H) :
    VDeg n (fun i => max (d i) (e i)) (fun v => G v + H v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun x => ih (hG.1 x) (hH.1 x), ?_⟩
      intro v
      obtain ⟨p, hp, hpe⟩ := hG.2 v
      obtain ⟨q, hq, hqe⟩ := hH.2 v
      refine ⟨p+q, (natDegree_add_le p q).trans (max_le_max hp hq), ?_⟩
      intro x; rw [eval_add, hpe, hqe]

#print axioms vdeg_add

theorem vdeg_mul {n : Nat} {d e : Fin n → Nat} {G H : (Fin n → K) → K}
    (hG : VDeg n d G) (hH : VDeg n e H) :
    VDeg n (fun i => d i + e i) (fun v => G v * H v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun x => ih (hG.1 x) (hH.1 x), ?_⟩
      intro v
      obtain ⟨p, hp, hpe⟩ := hG.2 v
      obtain ⟨q, hq, hqe⟩ := hH.2 v
      refine ⟨p*q, natDegree_mul_le.trans (Nat.add_le_add hp hq), ?_⟩
      intro x; rw [eval_mul, hpe, hqe]

#print axioms vdeg_mul

theorem vdeg_smul {n : Nat} {d : Fin n → Nat} {G : (Fin n → K) → K}
    (c : K) (hG : VDeg n d G) : VDeg n d (fun v => c * G v) := by
  simpa only [Nat.zero_add] using vdeg_mul (vdeg_const n (fun _ => 0) c) hG

#print axioms vdeg_smul

theorem vdeg_neg {n : Nat} {d : Fin n → Nat} {G : (Fin n → K) → K}
    (hG : VDeg n d G) : VDeg n d (fun v => -G v) := by
  simpa only [neg_one_mul] using vdeg_smul (-1) hG

#print axioms vdeg_neg

theorem vdeg_sub {n : Nat} {d e : Fin n → Nat} {G H : (Fin n → K) → K}
    (hG : VDeg n d G) (hH : VDeg n e H) :
    VDeg n (fun i => max (d i) (e i)) (fun v => G v - H v) := by
  simpa only [sub_eq_add_neg] using vdeg_add hG (vdeg_neg hH)

#print axioms vdeg_sub

theorem vdeg_pow {n : Nat} {d : Fin n → Nat} {G : (Fin n → K) → K}
    (hG : VDeg n d G) (k : Nat) : VDeg n (fun i => k*d i) (fun v => G v ^ k) := by
  induction k with
  | zero => simpa only [pow_zero, Nat.zero_mul] using vdeg_const n (fun _ => 0) (1 : K)
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using vdeg_mul ih hG

#print axioms vdeg_pow

theorem vdeg_sum {ι : Type} (s : Finset ι) {n : Nat} {d : Fin n → Nat}
    (G : ι → (Fin n → K) → K) (hG : ∀ i ∈ s, VDeg n d (G i)) :
    VDeg n d (fun v => ∑ i ∈ s, G i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using vdeg_const n d (0 : K)
  | @insert i s his ih =>
      simpa only [Finset.sum_insert his, max_self] using
        vdeg_add (hG i (Finset.mem_insert_self i s))
          (ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)))

#print axioms vdeg_sum

theorem vdeg_prod {ι : Type} (s : Finset ι) {n : Nat} (d : ι → Fin n → Nat)
    (G : ι → (Fin n → K) → K) (hG : ∀ i ∈ s, VDeg n (d i) (G i)) :
    VDeg n (fun c => ∑ i ∈ s, d i c) (fun v => ∏ i ∈ s, G i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using vdeg_const n (fun _ => 0) (1 : K)
  | @insert i s his ih =>
      simpa only [Finset.prod_insert his, Finset.sum_insert his] using
        vdeg_mul (hG i (Finset.mem_insert_self i s))
          (ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)))

#print axioms vdeg_prod

theorem vdeg_mlDeg {n : Nat} {d : Fin n → Nat} {G : (Fin n → K) → K}
    (hG : VDeg n d G) {e : Nat} (he : ∀ i, d i ≤ e) : MLDeg e n G := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun x => ih (hG.1 x) (fun i => he i.succ), ?_⟩
      intro v
      obtain ⟨p, hp, hpe⟩ := hG.2 v
      exact ⟨p, hp.trans (he 0), hpe⟩

#print axioms vdeg_mlDeg

/-- A univariate coordinate function has no degree in any other coordinate. -/
theorem vdeg_coord {n : Nat} (i : Fin n) (f : K → K) {k : Nat}
    (hf : ∃ p : K[X], p.natDegree ≤ k ∧ ∀ x, p.eval x = f x) :
    VDeg n (Pi.single i k) (fun v => f (v i)) := by
  classical
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          refine ⟨fun x => ?_, ?_⟩
          · exact vdeg_const n _ (f x)
          · intro v
            obtain ⟨p, hp, he⟩ := hf
            exact ⟨p, by simpa using hp, fun x => by simpa using he x⟩
      | succ i =>
          refine ⟨fun x => ?_, fun v => ⟨C (f (v i)), ?_, fun _ => eval_C⟩⟩
          · have hd : Fin.tail (Pi.single i.succ k : Fin (n+1) → Nat) = (Pi.single i k : Fin n → Nat) := by
              funext j
              simp only [Fin.tail, Pi.single_apply, Fin.succ_inj]
            rw [hd]
            exact ih i
          · simp only [natDegree_C, Nat.zero_le]

#print axioms vdeg_coord

/-- A product of affine coordinate factors has degree one exactly on its support. -/
theorem vdeg_prod_coord {n : Nat} (s : Finset (Fin n)) (f : Fin n → K → K)
    (hf : ∀ i ∈ s, ∃ p : K[X], p.natDegree ≤ 1 ∧ ∀ x, p.eval x = f i x) :
    VDeg n (fun i => if i ∈ s then 1 else 0) (fun v => ∏ i ∈ s, f i (v i)) := by
  classical
  have h := vdeg_prod s (fun i => Pi.single i 1) (fun i v => f i (v i))
    (fun i hi => vdeg_coord i (f i) (hf i hi))
  simpa only [Pi.single_apply, Finset.sum_ite_eq] using h

#print axioms vdeg_prod_coord

/-- Fixed residual lists preserve a common degree bound under summation. -/
theorem vdeg_list_foldl_add {n : Nat} {d : Fin n → Nat}
    (fs : List ((Fin n → K) → K)) (a : (Fin n → K) → K)
    (ha : VDeg n d a) (hf : ∀ f ∈ fs, VDeg n d f) :
    VDeg n d (fun v => (fs.map (fun f => f v)).foldl (· + ·) (a v)) := by
  induction fs generalizing a with
  | nil => simpa only [List.map_nil, List.foldl_nil] using ha
  | cons f fs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih (fun v => a v + f v)
      · simpa only [max_self] using vdeg_add ha (hf f (List.mem_cons_self ..))
      · intro g hg; exact hf g (List.mem_cons_of_mem _ hg)

#print axioms vdeg_list_foldl_add

theorem vdeg_list_getD {n : Nat} {d : Fin n → Nat}
    (fs : List ((Fin n → K) → K)) (hf : ∀ f ∈ fs, VDeg n d f) (i : Nat) :
    VDeg n d (fun v => (fs.map (fun f => f v)).getD i 0) := by
  induction fs generalizing i with
  | nil => simpa using vdeg_const n d (0 : K)
  | cons f fs ih =>
      cases i with
      | zero => simpa using hf f (List.mem_cons_self ..)
      | succ i => simpa using ih (fun g hg => hf g (List.mem_cons_of_mem _ hg)) i

#print axioms vdeg_list_getD
/-- One affine equality-weight factor. -/
def bitFactor (b : Bool) (x : K) : K := if b then x else 1-x

private theorem bitFactor_affine (b : Bool) :
    ∃ p : K[X], p.natDegree ≤ 1 ∧ ∀ x, p.eval x = bitFactor b x := by
  cases b
  · refine ⟨C 1-X, (natDegree_sub_le (C (1 : K)) X).trans (by simp), ?_⟩
    intro x; simp only [eval_sub, eval_C, eval_X, bitFactor, Bool.false_eq_true, if_false]
  · exact ⟨X, by simp, fun _ => eval_X⟩

#print axioms bitFactor_affine

theorem vdeg_bitFactor {n : Nat} {d : Fin n → Nat} {G : (Fin n → K) → K}
    (b : Bool) (hG : VDeg n d G) : VDeg n d (fun v => bitFactor b (G v)) := by
  cases b
  · simpa only [bitFactor, Bool.false_eq_true, if_false, Nat.zero_max] using
      vdeg_sub (vdeg_const n (fun _ => 0) (1 : K)) hG
  · exact hG

#print axioms vdeg_bitFactor

/-- Equality weights with the source's MSB-first coordinate ordering. -/
def bitWeight (n : Nat) (v : Fin n → K) (r : Nat) : K :=
  ∏ c : Fin n, bitFactor (r.testBit (n-1-c.val)) (v c)

theorem vdeg_bitWeight (n r : Nat) : VDeg n (fun _ => 1) (fun v : Fin n → K => bitWeight n v r) := by
  simpa only [bitWeight, Finset.mem_univ, if_true] using
    vdeg_prod_coord Finset.univ (fun c => bitFactor (r.testBit (n-1-c.val)))
      (fun c _ => bitFactor_affine _)

#print axioms vdeg_bitWeight

private theorem eqFactor_testBit (m k : Nat) (x : K) :
    (if m/2^k%2 = 0 then 1-x else x) = bitFactor (m.testBit k) x := by
  rcases Nat.mod_two_eq_zero_or_one (m/2^k) with h | h <;>
    simp [Nat.testBit_eq_decide_div_mod_eq, bitFactor, h]

#print axioms eqFactor_testBit

/-- Reversing the ten coordinate indices matches the literal R0 weights. -/
theorem selAt_eq_bitWeight (v : Fin 10 → K) (r : Fin 1024) :
    selAt v r = bitWeight 10 v r.val := by
  simp only [selAt, AspisR0.Opening.eqWeight, toR0, eqFactor_testBit, bitWeight]
  apply Fintype.prod_equiv (Fin.revPerm : Equiv.Perm (Fin 10))
  intro k
  have hr : (Fin.revPerm k : Fin 10) = ⟨9-k.val, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [hr]
  change bitFactor (r.val.testBit k.val) (v ⟨9-k.val, by omega⟩) =
    bitFactor (r.val.testBit (9-(9-k.val))) (v ⟨9-k.val, by omega⟩)
  rw [show 9-(9-k.val) = k.val by omega]

#print axioms selAt_eq_bitWeight

theorem vdeg_selAt (r : Fin 1024) : VDeg 10 (fun _ => 1) (fun v : Fin 10 → K => selAt v r) := by
  simp only [selAt_eq_bitWeight]
  exact vdeg_bitWeight 10 r.val

#print axioms vdeg_selAt

/-- The symbolic big-endian row code is a bijection in every dimension. -/
def rowCodeEquiv (n : Nat) : (Fin n → Bool) ≃ Fin (2^n) where
  toFun b := ⟨rowCode n b, rowCode_lt n b⟩
  invFun r := fun c => r.val.testBit (n-1-c.val)
  left_inv b := by funext c; exact rowCode_testBit n b c
  right_inv r := by
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < n
    · have hb := rowCode_testBit n (fun c => r.val.testBit (n-1-c.val))
        ⟨n-1-k, by omega⟩
      simpa only [show n-1-(n-1-k) = k by omega] using hb
    · have hp : (2 : Nat)^n ≤ 2^k := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (rowCode_lt n _) hp),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt hp)]

#print axioms rowCodeEquiv

/-- Equality weights form a partition of unity, proved by a cube bijection
and product-of-sums identity rather than expanding the row sum. -/
theorem bitWeight_sum (n : Nat) (v : Fin n → K) :
    (∑ r : Fin (2^n), bitWeight n v r.val) = 1 := by
  rw [← (rowCodeEquiv n).sum_comp (fun r => bitWeight n v r.val)]
  change (∑ b : Fin n → Bool, ∏ c : Fin n,
    bitFactor ((rowCode n b).testBit (n-1-c.val)) (v c)) = 1
  simp only [rowCode_testBit]
  rw [← Fintype.prod_sum (fun c (b : Bool) => bitFactor b (v c))]
  apply Finset.prod_eq_one
  intro c _
  simp only [Fintype.sum_bool, bitFactor, if_true, Bool.false_eq_true, if_false]
  ring

#print axioms bitWeight_sum

/-- An injective selection of coordinates preserves the affine support bound. -/
theorem vdeg_bitWeight_comp {n m : Nat} (ι : Fin m → Fin n) (hi : Function.Injective ι)
    (d : Fin n → Nat) (hd : ∀ i, 1 ≤ d (ι i)) (r : Nat) :
    VDeg n d (fun v : Fin n → K => bitWeight m (fun i => v (ι i)) r) := by
  classical
  apply vdeg_mono (vdeg_prod Finset.univ (fun i => Pi.single (ι i) 1)
    (fun i v => bitFactor (r.testBit (m-1-i.val)) (v (ι i)))
    (fun i _ => vdeg_coord (ι i) _ (bitFactor_affine _)))
  intro c
  by_cases hc : ∃ i, ι i = c
  · obtain ⟨i, rfl⟩ := hc
    simpa only [Pi.single_apply, hi.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, if_true] using hd i
  · have hn (i : Fin m) : c ≠ ι i := fun h => hc ⟨i, h.symm⟩
    simp only [Pi.single_apply, hn, if_false, Finset.sum_const_zero, Nat.zero_le]

#print axioms vdeg_bitWeight_comp

/-- High and low factors use disjoint source coordinates. -/
def eqHigh (v : Fin 10 → K) (h : Fin 64) : K := bitWeight 6 (fun c => v (c.castAdd 4)) h.val

def eqLow (v : Fin 10 → K) (l : Fin 16) : K := bitWeight 4 (fun c => v (c.natAdd 6)) l.val

def highDeg (c : Fin 10) : Nat := if c.val < 6 then 1 else 0

def lowDeg (c : Fin 10) : Nat := if c.val < 6 then 0 else 1

/-- `g2Row` has the verified layout 16*h+l, so its weight factors at bit 4. -/
theorem selAt_g2Row (v : Fin 10 → K) (h : Fin 64) (l : Fin 16) :
    selAt v (g2Row h l) = eqHigh v h * eqLow v l := by
  rw [selAt_eq_bitWeight]
  change (∏ c : Fin (6+4), bitFactor ((16*h.val+l.val).testBit (9-c.val)) (v c)) = _
  rw [Fin.prod_univ_add]
  congr 1
  · unfold eqHigh bitWeight
    apply Finset.prod_congr rfl
    intro c _
    have hb := Nat.testBit_two_pow_mul_add h.val (b := l.val) (i := 4) l.isLt (9-c.val)
    simp only [show (2 : Nat)^4 = 16 by norm_num, if_neg (show ¬ 9-c.val < 4 by omega),
      show 9-c.val-4 = 5-c.val by omega] at hb
    change bitFactor ((16*h.val+l.val).testBit (9-c.val)) (v (c.castAdd 4)) = _
    rw [hb]
  · unfold eqLow bitWeight
    apply Finset.prod_congr rfl
    intro c _
    have hb := Nat.testBit_two_pow_mul_add h.val (b := l.val) (i := 4) l.isLt (9-(6+c.val))
    simp only [show (2 : Nat)^4 = 16 by norm_num, if_pos (show 3-c.val < 4 by omega),
      show 9-(6+c.val) = 3-c.val by omega] at hb
    change bitFactor ((16*h.val+l.val).testBit (9-(6+c.val))) (v (c.natAdd 6)) = _
    rw [show 9-(6+c.val) = 3-c.val by omega, hb]

#print axioms selAt_g2Row

theorem eqHigh_sum (v : Fin 10 → K) : (∑ h, eqHigh v h) = 1 :=
  bitWeight_sum 6 (fun c => v (c.castAdd 4))

theorem eqLow_sum (v : Fin 10 → K) : (∑ l, eqLow v l) = 1 :=
  bitWeight_sum 4 (fun c => v (c.natAdd 6))

#print axioms eqHigh_sum
#print axioms eqLow_sum

theorem g2High_selAt (v : Fin 10 → K) (h : Fin 64) : g2High (selAt v) h = eqHigh v h := by
  simp only [g2High, selAt_g2Row, ← Finset.mul_sum, eqLow_sum, mul_one]

theorem g2Low_selAt (v : Fin 10 → K) (l : Fin 16) : g2Low (selAt v) l = eqLow v l := by
  simp only [g2Low, selAt_g2Row, ← Finset.sum_mul, eqHigh_sum, one_mul]

#print axioms g2High_selAt
#print axioms g2Low_selAt

theorem vdeg_eqHigh (h : Fin 64) : VDeg 10 highDeg (fun v : Fin 10 → K => eqHigh v h) := by
  apply vdeg_bitWeight_comp (fun c : Fin 6 => c.castAdd 4)
  · intro a b hab; exact Fin.ext (congrArg (fun q : Fin 10 => q.val) hab)
  · intro c; simp only [highDeg, Fin.val_castAdd, if_pos c.isLt, le_refl]

theorem vdeg_eqLow (l : Fin 16) : VDeg 10 lowDeg (fun v : Fin 10 → K => eqLow v l) := by
  apply vdeg_bitWeight_comp (fun c : Fin 4 => c.natAdd 6)
  · intro a b hab; apply Fin.ext; have := congrArg Fin.val hab; change 6+a.val = 6+b.val at this; omega
  · intro c; simp only [lowDeg, Fin.val_natAdd, if_neg (show ¬ 6+c.val < 6 by omega), le_refl]

#print axioms vdeg_eqHigh
#print axioms vdeg_eqLow

theorem vdeg_g2High (h : Fin 64) : VDeg 10 highDeg (fun v : Fin 10 → K => g2High (selAt v) h) := by
  simp only [g2High_selAt]; exact vdeg_eqHigh h

theorem vdeg_g2Low (l : Fin 16) : VDeg 10 lowDeg (fun v : Fin 10 → K => g2Low (selAt v) l) := by
  simp only [g2Low_selAt]; exact vdeg_eqLow l

#print axioms vdeg_g2High
#print axioms vdeg_g2Low

theorem vdeg_g2SumHigh (s c : Nat) (h : s+c ≤ 64) :
    VDeg 10 highDeg (fun v : Fin 10 → K => g2SumHigh (selAt v) s c h) := by
  simp only [g2SumHigh, g2_fold_add, zero_add, List.sum_ofFn]
  exact vdeg_sum Finset.univ _ (fun _ _ => vdeg_g2High _)

#print axioms vdeg_g2SumHigh

/-- A coordinate projection has degree one only at its own coordinate. -/
theorem vdeg_proj {n : Nat} (i : Fin n) :
    VDeg n (Pi.single i 1) (fun v : Fin n → K => v i) :=
  vdeg_coord i id ⟨X, by simp, fun _ => eval_X⟩

#print axioms vdeg_proj

/-- Composing equality factors adds the coordinate degree vectors. -/
theorem vdeg_bitWeight_inputs {n m : Nat} (d : Fin m → Fin n → Nat)
    (p : (Fin n → K) → Fin m → K) (hp : ∀ i, VDeg n (d i) (fun v => p v i)) (r : Nat) :
    VDeg n (fun c => ∑ i, d i c) (fun v => bitWeight m (p v) r) :=
  vdeg_prod Finset.univ d _ (fun i _ => vdeg_bitFactor _ (hp i))

#print axioms vdeg_bitWeight_inputs

/-- Carry after k low bits has degree one on precisely those low coordinates. -/
theorem vdeg_succCarry (k : Nat) (hk : k ≤ 10) :
    VDeg 10 (fun c => if 10-k ≤ c.val then 1 else 0) (fun v : Fin 10 → K => succCarry v k) := by
  classical
  induction k with
  | zero => exact vdeg_const 10 _ (1 : K)
  | succ k ih =>
      let i : Fin 10 := ⟨9-k, by omega⟩
      have h := vdeg_mul (vdeg_proj (K := K) i) (ih (by omega))
      simp only [succCarry, dif_pos (show k < 10 by omega)]
      apply vdeg_mono h
      intro c
      simp only [Pi.single_apply]
      split_ifs <;> simp_all only [Fin.ext_iff] <;> dsimp [i] at * <;> omega

#print axioms vdeg_succCarry

/-- Successor coordinate c depends affinely on each coordinate c..9. -/
theorem vdeg_successorPoint (c : Fin 10) :
    VDeg 10 (fun j => if c.val ≤ j.val then 1 else 0)
      (fun v : Fin 10 → K => successorPoint v c) := by
  classical
  have hc := vdeg_succCarry (K := K) (9-c.val) (by omega)
  have hp := vdeg_proj (K := K) c
  have hm := vdeg_mul hp hc
  apply vdeg_mono (vdeg_sub (vdeg_add hp hc) (vdeg_add hm hm))
  intro j
  simp only [Pi.single_apply]
  split_ifs <;> simp_all only [Fin.ext_iff] <;> omega

#print axioms vdeg_successorPoint

theorem vdeg_xor12Point (c : Fin 10) :
    VDeg 10 (Pi.single c 1) (fun v : Fin 10 → K => xor12Point v c) := by
  by_cases hc : c.val = 7 ∨ c.val = 6
  · simpa only [xor12Point, if_pos hc, bitFactor, Bool.false_eq_true, if_false] using
      vdeg_bitFactor false (vdeg_proj (K := K) c)
  · simpa only [xor12Point, if_neg hc] using vdeg_proj (K := K) c

#print axioms vdeg_xor12Point

theorem vdeg_selAt_successor (r : Fin 1024) :
    VDeg 10 (fun c => c.val+1) (fun v : Fin 10 → K => selAt (successorPoint v) r) := by
  simp only [selAt_eq_bitWeight]
  apply vdeg_mono (vdeg_bitWeight_inputs _ successorPoint vdeg_successorPoint r.val)
  intro c
  have hs : Finset.univ.filter (fun i : Fin 10 => i.val ≤ c.val) = Finset.Iic c := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    rfl
  rw [Finset.sum_boole, hs, Fin.card_Iic]
  simp

#print axioms vdeg_selAt_successor

theorem vdeg_selAt_xor12 (r : Fin 1024) :
    VDeg 10 (fun _ => 1) (fun v : Fin 10 → K => selAt (xor12Point v) r) := by
  simp only [selAt_eq_bitWeight]
  have h := vdeg_bitWeight_inputs (K := K) (fun c => Pi.single c 1) xor12Point vdeg_xor12Point r.val
  simpa only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

#print axioms vdeg_selAt_xor12

theorem vdeg_honestClaims_zero (t : Trace K) (l : Fin 29) :
    VDeg 10 (fun _ => 1) (fun v => honestClaims t v 0 l) := by
  change VDeg 10 _ (fun v => AspisR0.LinearDual.dot (selAt v) (t l))
  unfold AspisR0.LinearDual.dot
  apply vdeg_sum Finset.univ
  intro r _
  simpa only [mul_comm] using vdeg_smul (t l r) (vdeg_selAt r)

#print axioms vdeg_honestClaims_zero

theorem vdeg_honestClaims_one (t : Trace K) (l : Fin 29) :
    VDeg 10 (fun c => c.val+1) (fun v => honestClaims t v 1 l) := by
  change VDeg 10 _ (fun v => AspisR0.LinearDual.dot (selAt (successorPoint v)) (t l))
  unfold AspisR0.LinearDual.dot
  apply vdeg_sum Finset.univ
  intro r _
  simpa only [mul_comm] using vdeg_smul (t l r) (vdeg_selAt_successor r)

#print axioms vdeg_honestClaims_one

theorem vdeg_honestClaims_two (t : Trace K) (l : Fin 29) :
    VDeg 10 (fun _ => 1) (fun v => honestClaims t v 2 l) := by
  change VDeg 10 _ (fun v => AspisR0.LinearDual.dot (selAt (xor12Point v)) (t l))
  unfold AspisR0.LinearDual.dot
  apply vdeg_sum Finset.univ
  intro r _
  simpa only [mul_comm] using vdeg_smul (t l r) (vdeg_selAt_xor12 r)

#print axioms vdeg_honestClaims_two

theorem vdeg_eqValue (zc : Fin 10 → K) :
    VDeg 10 (fun _ => 1) (fun v => eqValue zc v) := by
  unfold eqValue
  apply (vdeg_prod_coord Finset.univ (fun c x => 1-zc c-x+zc c*x+zc c*x) ?_)
  intro c _
  refine ⟨C (1-zc c) + C (zc c+zc c-1)*X, ?_, ?_⟩
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · simp only [natDegree_C]; omega
    · apply natDegree_mul_le.trans
      simp only [natDegree_C, natDegree_X]; omega
  · intro x
    simp only [eval_add, eval_mul, eval_C, eval_X]
    ring

#print axioms vdeg_eqValue

theorem vdeg_pack4 {n : Nat} {d : Fin n → Nat} {F : Subfield K} (B : PackBasis F)
    (v : (Fin n → K) → Fin 4 → K) (hv : ∀ i, VDeg n d (fun x => v x i)) :
    VDeg n d (fun x => pack4 B (v x)) := by
  simpa only [pack4, max_self] using
    vdeg_add (vdeg_add (vdeg_add (hv 0) (vdeg_smul B.i (hv 1)))
      (vdeg_smul B.u (hv 2))) (vdeg_smul (B.i*B.u) (hv 3))

#print axioms vdeg_pack4

end R0P.SemDegree
end
