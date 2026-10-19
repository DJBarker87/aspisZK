import R0P.SemD3

/-! Honest claims at Boolean rows. Bit identities and product/sum identities
are symbolic; no rows, blocks, tables or permutations are enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R0P.SemSource
open Polynomial Sumcheck AspisR0.Opening AspisR0.LinearDual
variable {K : Type} [Field K]

private theorem eqFactor_bool (m k : Nat) (b : Bool) :
    (if m / 2^k % 2 = 0 then 1 - (if b then 1 else 0) else
      (if b then 1 else 0) : K) = if m.testBit k = b then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one (m / 2^k) with h | h <;>
    cases b <;> simp [Nat.testBit_eq_decide_div_mod_eq, h]

#print axioms eqFactor_bool

/-- Boolean equality weights select precisely the big-endian encoded row. -/
theorem selAt_ofBool (b : Fin 10 → Bool) :
    selAt (ofBool b : Fin 10 → K) = rowSel (rowOf b) := by
  funext r
  have hbits : (∀ k : Fin 10, r.val.testBit k.val = b ⟨9-k.val, by omega⟩) ↔
      r = rowOf b := by
    constructor
    · intro h
      have hb : rowBits r = b := by
        funext i
        have hi := h ⟨9-i.val, by omega⟩
        have he : (⟨9-(9-i.val), by omega⟩ : Fin 10) = i := Fin.ext (by change 9-(9-i.val) = i.val; omega)
        simpa only [rowBits, he] using hi
      obtain ⟨b', hr⟩ := rowOf_surjective r
      have he : b' = b := by rw [← hr, rowBits_rowOf] at hb; exact hb
      exact hr.symm.trans (congrArg rowOf he)
    · intro h
      subst r
      intro k
      have hb := congrFun (rowBits_rowOf b) ⟨9-k.val, by omega⟩
      change (rowOf b).val.testBit (9-(9-k.val)) = _ at hb
      simpa only [show 9-(9-k.val) = k.val by omega] using hb
  simp only [selAt, eqWeight, toR0, ofBool, eqFactor_bool, Fintype.prod_boole,
    hbits, rowSel]

#print axioms selAt_ofBool
/-- A one-row selector evaluates the selected trace coordinate. -/
theorem dot_rowSel (r : Fin 1024) (w : Fin 1024 → K) :
    AspisR0.LinearDual.dot (rowSel r) w = w r := by
  simp only [AspisR0.LinearDual.dot, rowSel, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

#print axioms dot_rowSel
/-- A binary digit embedded in the generic field. -/
def bitVal (m k : Nat) : K := if m.testBit k then 1 else 0

/-- Carry into bit k, expressed without enumerating any row. -/
def bitCarry (m k : Nat) : K := ∏ j ∈ Finset.range k, bitVal m j

private theorem bitCarry_bit (a k : Nat) (b : Bool) :
    bitCarry (K := K) (Nat.bit b a) (k+1) = (if b then 1 else 0) * bitCarry a k := by
  simp only [bitCarry, Finset.prod_range_succ', bitVal, Nat.testBit_bit_succ,
    Nat.testBit_bit_zero]
  exact mul_comm _ _

#print axioms bitCarry_bit

/-- Binary increment is XOR with the carry into the selected bit. -/
theorem bitVal_succ (m k : Nat) :
    bitVal (K := K) (m+1) k = bitVal m k + bitCarry m k -
      (bitVal m k * bitCarry m k + bitVal m k * bitCarry m k) := by
  induction k generalizing m with
  | zero =>
      have hb : (m+1).testBit 0 = !(m.testBit 0) := by
        simpa only [Nat.pow_zero, Nat.add_comm] using Nat.testBit_two_pow_add_eq m 0
      simp only [bitCarry, Finset.range_zero, Finset.prod_empty, bitVal, hb]
      cases m.testBit 0 <;> simp
  | succ k ih =>
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm
      · obtain ⟨a, rfl⟩ : ∃ a, m = Nat.bit false a :=
          ⟨m/2, by simp only [Nat.bit_false]; omega⟩
        have ha : Nat.bit false a + 1 = Nat.bit true a := by
          simp only [Nat.bit_false, Nat.bit_true]
        rw [ha, bitCarry_bit]
        simp only [bitVal, Nat.testBit_bit_succ, Bool.false_eq_true, if_false,
          zero_mul, mul_zero, add_zero, sub_zero]
      · obtain ⟨a, rfl⟩ : ∃ a, m = Nat.bit true a :=
          ⟨m/2, by simp only [Nat.bit_true]; omega⟩
        have ha : Nat.bit true a + 1 = Nat.bit false (a+1) := by
          simp only [Nat.bit_false, Nat.bit_true]; omega
        rw [ha, bitCarry_bit]
        simpa only [bitVal, Nat.testBit_bit_succ, if_true, one_mul]
          using ih a

#print axioms bitVal_succ

/-- The source's reversed carry recurrence is the binary carry product. -/
theorem succCarry_ofBool (b : Fin 10 → Bool) (k : Nat) (hk : k ≤ 10) :
    succCarry (ofBool b : Fin 10 → K) k = bitCarry (rowOf b).val k := by
  induction k with
  | zero => simp only [succCarry, bitCarry, Finset.range_zero, Finset.prod_empty]
  | succ k ih =>
      rw [succCarry, dif_pos (show k < 10 by omega), ih (by omega)]
      have hb := congrFun (rowBits_rowOf b) ⟨9-k, by omega⟩
      change (rowOf b).val.testBit (9-(9-k)) = _ at hb
      rw [show 9-(9-k) = k by omega] at hb
      simp only [ofBool, bitCarry, Finset.prod_range_succ, bitVal, hb]
      exact mul_comm _ _

#print axioms succCarry_ofBool

/-- The literal polynomial successor agrees with increment modulo 1024
on Boolean inputs. -/
theorem successorPoint_ofBool (b : Fin 10 → Bool) :
    successorPoint (ofBool b : Fin 10 → K) = ofBool (rowBits (succRow (rowOf b))) := by
  funext c
  have hb : bitVal (K := K) (rowOf b).val (9-c.val) = ofBool b c := by
    change (if rowBits (rowOf b) c then 1 else 0) = _
    rw [rowBits_rowOf]
    rfl
  have hs := bitVal_succ (K := K) (rowOf b).val (9-c.val)
  rw [hb, ← succCarry_ofBool b _ (by omega)] at hs
  change successorPoint (ofBool b) c =
    (if (((rowOf b).val+1)%1024).testBit (9-c.val) then 1 else 0)
  have hmod := Nat.testBit_mod_two_pow ((rowOf b).val+1) 10 (9-c.val)
  rw [show (2 : Nat)^10 = 1024 by norm_num] at hmod
  rw [hmod]
  simp only [show 9-c.val < 10 by omega, decide_true, Bool.true_and]
  exact hs.symm

#print axioms successorPoint_ofBool

/-- The source's two toggled coordinates are exactly row bits 2 and 3. -/
theorem xor12Point_ofBool (b : Fin 10 → Bool) :
    xor12Point (ofBool b : Fin 10 → K) = ofBool (rowBits (xor12Row (rowOf b))) := by
  funext c
  have hb := congrFun (rowBits_rowOf b) c
  change (rowOf b).val.testBit (9-c.val) = b c at hb
  have h12 : (12 : Nat) = 2^2 ||| 2^3 := rfl
  have hbit : (12 : Nat).testBit (9-c.val) = decide (c.val = 7 ∨ c.val = 6) := by
    rw [h12, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow]
    have he : (2 = 9-c.val ∨ 3 = 9-c.val) ↔ (c.val = 7 ∨ c.val = 6) := by omega
    simp only [← Bool.decide_or, he]
  change (if c.val = 7 ∨ c.val = 6 then 1 - (if b c then 1 else 0) else
      (if b c then 1 else 0)) =
    (if ((rowOf b).val ^^^ 12).testBit (9-c.val) then 1 else 0)
  rw [Nat.testBit_xor, hb, hbit]
  by_cases hc : c.val = 7 ∨ c.val = 6 <;> cases b c <;> simp [hc]

#print axioms xor12Point_ofBool

/-- Inverse direction of the row/bit equivalence. -/
theorem rowOf_rowBits (r : Fin 1024) : rowOf (rowBits r) = r := by
  obtain ⟨b, rfl⟩ := rowOf_surjective r
  rw [rowBits_rowOf]

#print axioms rowOf_rowBits

/-- Honest claims are the three literal row openings on the Boolean cube. -/
theorem honestClaims_ofBool (t : Trace K) (b : Fin 10 → Bool) :
    honestClaims t (ofBool b) = fun j l => match j with
      | 0 => t l (rowOf b)
      | 1 => t l (succRow (rowOf b))
      | 2 => t l (xor12Row (rowOf b)) := by
  have hs (p : Fin 10 → K) : eqWeight (toR0 p) = selAt p := rfl
  funext j l
  fin_cases j <;>
    simp only [honestClaims, openingPoints, successorPoint_ofBool, xor12Point_ofBool,
      hs, selAt_ofBool, dot_rowSel, rowOf_rowBits]

#print axioms honestClaims_ofBool

private theorem prod_eqwB (n : Nat) (z : Fin n → K) (b : Fin n → Bool) :
    (∏ c : Fin n, if b c then z c else 1-z c) = eqwB n z b := by
  induction n with
  | zero => simp only [Fin.prod_univ_zero, eqwB]
  | succ n ih =>
      rw [Fin.prod_univ_succ, eqwB, ← ih]
      rfl

#print axioms prod_eqwB

/-- The product equality polynomial agrees with the recursive Boolean weight. -/
theorem eqValue_ofBool (zc : Fin 10 → K) (b : Fin 10 → Bool) :
    eqValue zc (ofBool b) = eqwB 10 zc b := by
  rw [eqValue, ← prod_eqwB]
  apply Finset.prod_congr rfl
  intro c _
  unfold ofBool
  cases b c <;> simp

#print axioms eqValue_ofBool

/-- The terminal's active selector is the literal Boolean-row selector. -/
theorem activeAt_ofBool (b : Fin 10 → Bool) :
    activeAt (ofBool b : Fin 10 → K) = copyActiveLiteral (copySelectors (rowSel (rowOf b))) := by
  rw [activeAt, selAt_ofBool]

#print axioms activeAt_ofBool
/-- Honest Boolean claims turn the terminal into the production lane sum
and the two literal H1 helper terms, with no semantic premise. -/
theorem honestRows (pub : Public K) {F : Subfield K} (B : PackBasis F)
    (t : Trace K) : HonestRows pub B t := by
  intro pre b
  simp only [virtualPoly, terminalValue, honestClaims_ofBool, eqValue_ofBool,
    selAt_ofBool, activeAt_ofBool, lanesComp, laneOf_eq_laneAt, rowOpenings]
  ring

#print axioms honestRows
end R0P.SemSource
end
