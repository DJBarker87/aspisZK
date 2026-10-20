import CuSavingsLibraLoop
import CuSavingsPowerLoop

/-! Source-shaped semantic loops for the two retained Libra implementations.
This consumes the power-table, literal-index, and tensor-factorization proofs.
The models use total Nat/list operations over an arbitrary commutative
semiring. They are handwritten models, not an Aeneas emission: the concrete
field interpretation, allocation/access failures and Rust caller binding are
explicitly still required. No nonzero input assumptions are used. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsLibra
variable {R : Type} [CommSemiring R]

def powerAt (q : R) (n i : Nat) : R :=
  ((CuSavingsPowerLoop.run q 1 n).1[i]?).getD 0

theorem powerAt_eq (q : R) (n i : Nat) (hi : i < n) :
    powerAt q n i = q^i := by
  simp only [powerAt, CuSavingsPowerLoop.read q n i hi, Option.getD_some]

theorem fold_add_sum {T : Type} (xs : List T) (f : T → R) (init : R) :
    xs.foldl (fun acc x => acc + f x) init = init + (xs.map f).sum := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

def referenceProgramBlock (a b : Nat → R) (c q0 q1 : R) (j : Nat) : R :=
  (List.range 16).foldl (fun acc s =>
    let index := 16*j+s
    if index < 56 then
      acc + literalLow a b c s * powerAt (if index/28 = 0 then q0 else q1) 28 (index%28)
    else acc) 0

theorem referenceProgramBlock_eq (a b : Nat → R) (c q0 q1 : R) (j : Nat) :
    referenceProgramBlock a b c q0 q1 j = literalBlock a b c q0 q1 j := by
  have step : (fun acc s =>
      let index := 16*j+s
      if index < 56 then
        acc + literalLow a b c s * powerAt (if index/28 = 0 then q0 else q1) 28 (index%28)
      else acc) = (fun acc s => acc + literalCell a b c q0 q1 j s) := by
    funext acc s
    dsimp only
    by_cases hi : 16*j+s < 56
    · have hm : (16*j+s)%28 < 28 := Nat.mod_lt _ (by omega)
      simp only [hi, if_true, literalCell, powerAt_eq _ 28 _ hm]
    · simp only [hi, if_false, literalCell, add_zero]
  unfold referenceProgramBlock
  rw [step, fold_add_sum, zero_add]
  rfl

def referenceProgram (a b : Nat → R) (c q0 q1 : R) : R × R × R × R :=
  (referenceProgramBlock a b c q0 q1 0, referenceProgramBlock a b c q0 q1 1,
   referenceProgramBlock a b c q0 q1 2, referenceProgramBlock a b c q0 q1 3)

theorem referenceProgram_eq_literal (a b : Nat → R) (c q0 q1 : R) :
    referenceProgram a b c q0 q1 = literalWeights a b c q0 q1 := by
  simp only [referenceProgram, literalWeights, referenceProgramBlock_eq]

/-- Source array accesses are in range on each of the admitted four blocks;
the largest natural index is also far below the 32-bit usize bound. This is
an arithmetic admission fact, not a theorem about checked machine execution. -/
theorem reference_indices (j s : Nat) (hj : j < 4) (hs : s < 16) :
    16*j+s < 64 ∧
      (16*j+s < 56 → (16*j+s)/28 < 2 ∧ (16*j+s)%28 < 28) := by
  omega

def programLow (a : Nat → R) (c q : R) : R :=
  (List.range 4).foldl (fun acc s => acc + a s * powerAt q 4 s) 0 * c

theorem programLow_eq (a : Nat → R) (c q : R) :
    programLow a c q = lowRun a c q := by
  unfold programLow
  rw [fold_add_sum, zero_add]
  calc
    _ = (((List.range 4).map (fun s => a s * powerAt q 4 s * c))).sum :=
      (List.sum_map_mul_right _ _ _).symm
    _ = lowRun a c q := by
      unfold lowRun
      congr 1
      apply List.map_congr_left
      intro s hs
      rw [powerAt_eq q 4 s (List.mem_range.mp hs)]
      ring

def programPowers (q : R) : R × R × R × R :=
  let q2 := powerAt q 4 2
  let q4 := q2*q2
  let q8 := q4*q4
  let q12 := q8*q4
  let q16 := q8*q8
  (q4,q8,q12,q16)

theorem programPowers_eq (q : R) :
    programPowers q = (q^4,q^8,q^12,q^16) := by
  unfold programPowers
  rw [powerAt_eq q 4 2 (by omega)]
  simp only [← pow_add]

def programHigh (q : R) (r : Nat) : R :=
  let p := programPowers q
  if r=0 then 1 else if r=1 then p.1 else if r=2 then p.2.1 else p.2.2.1

theorem programHigh_eq (q : R) (r : Nat) (hr : r < 4) :
    programHigh q r = q^(4*r) := by
  have cases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases cases with h | h | h | h <;> subst r <;>
    simp [programHigh, programPowers_eq]

def programTerm (b : Nat → R) (c q : R) (r : Nat) : R :=
  b r * programHigh q r * c

theorem programTerm_eq (b : Nat → R) (c q : R) (r : Nat) (hr : r < 4) :
    programTerm b c q r = b r*c*q^(4*r) := by
  rw [programTerm, programHigh_eq q r hr]
  ring

/-- The five expressions assigned by one side: two from side zero, three
from side one, with the middle entry added into the prior side-zero value. -/
def programSide (a b : Nat → R) (c q : R) : R × R × R × R × R :=
  let low := programLow a c q
  let p := programPowers q
  let terms := programTerm b c q
  let first2 := terms 0 + terms 1
  let first3 := first2 + terms 2
  let all := first3 + terms 3
  (low*all,low*first3*p.2.2.2,low*(b 3*c),
   low*all*p.1,low*first2*(p.2.2.2*p.1))

def factoredProgram (a b : Nat → R) (c q0 q1 : R) : R × R × R × R :=
  let side0 := programSide a b c q0
  let side1 := programSide a b c q1
  (side0.1,side0.2.1+side1.2.2.1,side1.2.2.2.1,side1.2.2.2.2)

theorem factoredProgram_eq_factored (a b : Nat → R) (c q0 q1 : R) :
    factoredProgram a b c q0 q1 = factoredWeights a b c q0 q1 := by
  unfold factoredProgram programSide
  simp only [programLow_eq, programPowers_eq,
    programTerm_eq b c q0 0 (by omega), programTerm_eq b c q0 1 (by omega),
    programTerm_eq b c q0 2 (by omega), programTerm_eq b c q0 3 (by omega),
    programTerm_eq b c q1 0 (by omega), programTerm_eq b c q1 1 (by omega),
    programTerm_eq b c q1 2 (by omega), programTerm_eq b c q1 3 (by omega)]
  rfl

theorem factoredProgram_eq_referenceProgram (a b : Nat → R) (c q0 q1 : R) :
    factoredProgram a b c q0 q1 = referenceProgram a b c q0 q1 :=
  (factoredProgram_eq_factored a b c q0 q1).trans
    ((factored_eq_literal a b c q0 q1).trans (referenceProgram_eq_literal a b c q0 q1).symm)

/-- Original caller tensor scaling equals the split scaling used above. -/
theorem callerLow_eq (a b : Nat → R) (c : R) (s : Nat) :
    a (s%4)*b (s/4)*(c*c) = literalLow a b c s := by
  unfold literalLow
  ring

#print axioms referenceProgram_eq_literal
#print axioms programLow_eq
#print axioms programPowers_eq
#print axioms factoredProgram_eq_referenceProgram
#print axioms callerLow_eq
end AspisR1.CuSavingsLibra
