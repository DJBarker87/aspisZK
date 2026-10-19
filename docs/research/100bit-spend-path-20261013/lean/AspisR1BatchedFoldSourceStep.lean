import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace AspisR1BatchedFoldSourceStep

def modulus : Nat := 2 ^ 31 - 1
def limbBase : Nat := 2 ^ 31
def fold (x : Nat) : Nat := x % limbBase + x / limbBase

theorem modulus_succ : modulus + 1 = limbBase := by
  norm_num [modulus, limbBase]

theorem product_bound {a b : Nat} (ha : a < modulus) (hb : b < modulus) :
    a * b ≤ (2 ^ 31 - 2) ^ 2 := by
  have ha' : a ≤ 2 ^ 31 - 2 := by change a < 2 ^ 31 - 1 at ha; omega
  have hb' : b ≤ 2 ^ 31 - 2 := by change b < 2 ^ 31 - 1 at hb; omega
  have hmul := Nat.mul_le_mul ha' hb'
  simpa [pow_two] using hmul

theorem fold_preserves_mod (x : Nat) : fold x % modulus = x % modulus := by
  have hdiv : x % limbBase + limbBase * (x / limbBase) = x := Nat.mod_add_div _ _
  have hbase : limbBase = modulus + 1 := by rw [modulus_succ]
  have hx : x = fold x + modulus * (x / limbBase) := by
    have hlimb : limbBase = 2147483648 := by norm_num [limbBase]
    have hmodulus : modulus = 2147483647 := by norm_num [modulus]
    dsimp [fold] at *
    rw [hlimb] at hdiv ⊢
    rw [hmodulus]
    omega
  calc
    fold x % modulus = (fold x + modulus * (x / limbBase)) % modulus :=
      (Nat.add_mul_mod_self_left (fold x) modulus (x / limbBase)).symm
    _ = x % modulus := by rw [← hx]

theorem fold_lt_two34 {x : Nat} (hx : x < 2 ^ 64) : fold x < 2 ^ 34 := by
  have hmod : x % limbBase < limbBase := Nat.mod_lt _ (by norm_num [limbBase])
  have hdiv : x / limbBase < 2 ^ 33 := by
    apply Nat.div_lt_iff_lt_mul (by norm_num [limbBase]) |>.2
    calc
      x < 2 ^ 64 := hx
      _ = (2 ^ 33) * limbBase := by norm_num [limbBase, pow_add]
  unfold fold
  have : limbBase = 2 ^ 31 := rfl
  omega

/-- One source-shaped four-query batch: each term is a product of canonical
M31 limbs; the retained residue and every pre-fold prefix fit in UInt64.
The fold preserves the field residue and restores the group-boundary limit. -/
theorem four_query_batch {r a b c d : Nat}
    (hr : r < 2 ^ 34)
    (ha : a ≤ (2 ^ 31 - 2) ^ 2) (hb : b ≤ (2 ^ 31 - 2) ^ 2)
    (hc : c ≤ (2 ^ 31 - 2) ^ 2) (hd : d ≤ (2 ^ 31 - 2) ^ 2) :
    r + a + b + c + d < 2 ^ 64 ∧
    r + a + b + c < 2 ^ 64 ∧
    r + a + b < 2 ^ 64 ∧
    r + a < 2 ^ 64 ∧
    fold (r + a + b + c + d) < 2 ^ 34 ∧
    fold (r + a + b + c + d) % modulus = (r + a + b + c + d) % modulus := by
  have htotal : r + a + b + c + d < 2 ^ 64 := by omega
  refine ⟨htotal, ?_, ?_, ?_, fold_lt_two34 htotal, fold_preserves_mod _⟩ <;> omega

theorem four_canonical_products {r : Nat} (hr : r < 2 ^ 34)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (ha0 : a0 < modulus) (ha1 : a1 < modulus)
    (ha2 : a2 < modulus) (ha3 : a3 < modulus)
    (hb0 : b0 < modulus) (hb1 : b1 < modulus)
    (hb2 : b2 < modulus) (hb3 : b3 < modulus) :
    r + a0*b0 + a1*b1 + a2*b2 + a3*b3 < 2 ^ 64 := by
  have h0 := product_bound ha0 hb0
  have h1 := product_bound ha1 hb1
  have h2 := product_bound ha2 hb2
  have h3 := product_bound ha3 hb3
  have h0' : a0*b0 ≤ (2 ^ 31 - 2) ^ 2 := h0
  have h1' : a1*b1 ≤ (2 ^ 31 - 2) ^ 2 := h1
  have h2' : a2*b2 ≤ (2 ^ 31 - 2) ^ 2 := h2
  have h3' : a3*b3 ≤ (2 ^ 31 - 2) ^ 2 := h3
  omega

structure Batch where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

def productCap : Nat := (2 ^ 31 - 2) ^ 2
def batchTotal (x : Batch) : Nat := x.a + x.b + x.c + x.d
def batchValid (x : Batch) : Prop :=
  x.a ≤ productCap ∧ x.b ≤ productCap ∧ x.c ≤ productCap ∧ x.d ≤ productCap

def runBatches (r : Nat) : List Batch → Nat
  | [] => r
  | x :: xs => runBatches (fold (r + batchTotal x)) xs

def totalBatches : List Batch → Nat
  | [] => 0
  | x :: xs => batchTotal x + totalBatches xs

/-- Repeated source-shaped groups retain a bounded UInt64 accumulator at each
group boundary. The per-query prefixes are bounded by `four_query_batch`. -/
theorem runBatches_lt (xs : List Batch) (hxs : ∀ x ∈ xs, batchValid x) :
    ∀ r, r < 2 ^ 34 → runBatches r xs < 2 ^ 34 := by
  induction xs with
  | nil => intro r hr; simpa [runBatches] using hr
  | cons x xs ih =>
      intro r hr
      have hx := hxs x (by simp)
      have hsum : r + batchTotal x < 2 ^ 64 := by
        rcases hx with ⟨ha, hb, hc, hd⟩
        have hcap : productCap = 4611686009837453316 := by norm_num [productCap]
        rw [hcap] at ha hb hc hd
        unfold batchTotal
        norm_num at ha hb hc hd ⊢
        omega
      have hfold : fold (r + batchTotal x) < 2 ^ 34 := fold_lt_two34 hsum
      apply ih (fun y hy => hxs y (by simp [hy])) (fold (r + batchTotal x)) hfold

/-- The completed four-query folds preserve the exact residue of the original
unreduced sum, for any number of batches. -/
theorem runBatches_mod (xs : List Batch) :
    ∀ r, runBatches r xs % modulus = (r + totalBatches xs) % modulus := by
  induction xs with
  | nil => intro r; simp [runBatches, totalBatches]
  | cons x xs ih =>
      intro r
      have hfold : fold (r + batchTotal x) % modulus = (r + batchTotal x) % modulus :=
        fold_preserves_mod _
      calc
        runBatches (fold (r + batchTotal x)) xs % modulus =
            (fold (r + batchTotal x) + totalBatches xs) % modulus := ih _
        _ = ((fold (r + batchTotal x) % modulus) + totalBatches xs % modulus) % modulus := by
          rw [Nat.add_mod]
        _ = (((r + batchTotal x) % modulus) + totalBatches xs % modulus) % modulus := by
          rw [hfold]
        _ = (r + batchTotal x + totalBatches xs) % modulus := by
          rw [Nat.add_mod, Nat.add_mod]
          simp [Nat.add_assoc]
        _ = (r + totalBatches (x :: xs)) % modulus := by simp [totalBatches, Nat.add_assoc]

/-- One push to the transaction-local raw lane. The condition models the
source's periodic flush point; the exact UInt64 bitmask correspondence is a
separate machine-level source-repin fact. -/
def sourcePush (terms raw product : Nat) : Nat :=
  if terms % 4 = 3 then fold (raw + product) else raw + product

theorem sourcePush_mod (terms raw product : Nat) :
    sourcePush terms raw product % modulus = (raw + product) % modulus := by
  unfold sourcePush
  split <;> simp [fold_preserves_mod]

theorem sourceFourPush (terms raw a b c d : Nat)
    (hboundary : terms % 4 = 0)
    (hr : raw < 2 ^ 34)
    (ha : a ≤ (2 ^ 31 - 2) ^ 2) (hb : b ≤ (2 ^ 31 - 2) ^ 2)
    (hc : c ≤ (2 ^ 31 - 2) ^ 2) (hd : d ≤ (2 ^ 31 - 2) ^ 2) :
    let r1 := sourcePush terms raw a
    let r2 := sourcePush (terms+1) r1 b
    let r3 := sourcePush (terms+2) r2 c
    let r4 := sourcePush (terms+3) r3 d
    r1 < 2 ^ 64 ∧ r2 < 2 ^ 64 ∧ r3 < 2 ^ 64 ∧
      r4 < 2 ^ 34 ∧ r4 % modulus = (raw+a+b+c+d) % modulus := by
  have h0 : terms % 4 ≠ 3 := by omega
  have h1 : (terms+1) % 4 ≠ 3 := by omega
  have h2 : (terms+2) % 4 ≠ 3 := by omega
  have h3 : (terms+3) % 4 = 3 := by omega
  have hb := four_query_batch hr ha hb hc hd
  rcases hb with ⟨hfinal, h3safe, h2safe, h1safe, hfold, hmod⟩
  simp only [sourcePush, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
  exact ⟨h1safe, h2safe, h3safe, hfold, by simpa [Nat.add_assoc] using hmod⟩

#print axioms sourcePush_mod
#print axioms sourceFourPush

#print axioms product_bound
#print axioms four_query_batch
#print axioms runBatches_lt
#print axioms runBatches_mod

end AspisR1BatchedFoldSourceStep
