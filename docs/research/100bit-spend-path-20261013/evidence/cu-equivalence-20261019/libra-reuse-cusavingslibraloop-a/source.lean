import CuSavingsLibra

/-! The literal 16-slot, 56-term Libra loop, including the index/28 switch
and final eight inactive slots. This proves its equality with the already
checked division-free factorization. Machine fields and the extracted caller
are separate obligations; this file makes no assumption that the cut is right. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsLibra
variable {R : Type} [CommSemiring R]

def sumRange (n : Nat) (f : Nat → R) : R := ((List.range n).map f).sum

theorem sumRange_add (n m : Nat) (f : Nat → R) :
    sumRange (n+m) f = sumRange n f + sumRange m (fun i => f (n+i)) := by
  simp only [sumRange, List.range_add, List.map_append, List.sum_append,
    List.map_map, Function.comp_def]

theorem sumRange_succ (n : Nat) (f : Nat → R) :
    sumRange (n+1) f = sumRange n f + f n := by
  simp [sumRange, List.range_succ]

theorem sumRange_mul (n w : Nat) (f : Nat → R) :
    sumRange (n*w) f = sumRange n (fun r => sumRange w (fun s => f (r*w+s))) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [Nat.succ_mul, sumRange_add, ih, sumRange_succ]

theorem sumRange_congr (n : Nat) (f g : Nat → R)
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  unfold sumRange
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => (0 : R)) = 0 := by
  simp [sumRange]

theorem sumRange_one (f : Nat → R) : sumRange 1 f = f 0 := by
  simp [sumRange]

def literalLow (a b : Nat → R) (c : R) (k : Nat) : R :=
  (a (k%4)*c)*(b (k/4)*c)

def literalCell (a b : Nat → R) (c q0 q1 : R) (j k : Nat) : R :=
  if 16*j+k < 56 then
    literalLow a b c k * (if (16*j+k)/28 = 0 then q0 else q1)^((16*j+k)%28)
  else 0

def literalBlock (a b : Nat → R) (c q0 q1 : R) (j : Nat) : R :=
  sumRange 16 (literalCell a b c q0 q1 j)

def literalWeights (a b : Nat → R) (c q0 q1 : R) : R × R × R × R :=
  (literalBlock a b c q0 q1 0, literalBlock a b c q0 q1 1,
   literalBlock a b c q0 q1 2, literalBlock a b c q0 q1 3)

theorem literalLow_row (a b : Nat → R) (c : R) (r s : Nat) (hs : s < 4) :
    literalLow a b c (r*4+s) = (a s*c)*(b r*c) := by
  have hm : (r*4+s)%4 = s := by omega
  have hd : (r*4+s)/4 = r := by omega
  simp only [literalLow, hm, hd]

theorem literalCell_first (a b : Nat → R) (c q0 q1 : R) (r s : Nat)
    (hr : r < 4) (hs : s < 4) :
    literalCell a b c q0 q1 0 (r*4+s) = (a s*c)*(b r*c)*q0^(0+4*r+s) := by
  have hi : 16*0+(r*4+s) < 56 := by omega
  have hd : (16*0+(r*4+s))/28 = 0 := by omega
  have hm : (16*0+(r*4+s))%28 = 0+4*r+s := by omega
  simp only [literalCell, hi, if_true, hd, hm, literalLow_row a b c r s hs]

theorem literalCell_second_head (a b : Nat → R) (c q0 q1 : R) (r s : Nat)
    (hr : r < 3) (hs : s < 4) :
    literalCell a b c q0 q1 1 (r*4+s) = (a s*c)*(b r*c)*q0^(16+4*r+s) := by
  have hi : 16*1+(r*4+s) < 56 := by omega
  have hd : (16*1+(r*4+s))/28 = 0 := by omega
  have hm : (16*1+(r*4+s))%28 = 16+4*r+s := by omega
  simp only [literalCell, hi, if_true, hd, hm, literalLow_row a b c r s hs]

theorem literalCell_second_tail (a b : Nat → R) (c q0 q1 : R) (s : Nat)
    (hs : s < 4) :
    literalCell a b c q0 q1 1 (3*4+s) = (a s*c)*(b 3*c)*q1^s := by
  have hi : 16*1+(3*4+s) < 56 := by omega
  have hd : (16*1+(3*4+s))/28 ≠ 0 := by omega
  have hm : (16*1+(3*4+s))%28 = s := by omega
  simp only [literalCell, hi, if_true, hd, if_false, hm, literalLow_row a b c 3 s hs]

theorem literalCell_third (a b : Nat → R) (c q0 q1 : R) (r s : Nat)
    (hr : r < 4) (hs : s < 4) :
    literalCell a b c q0 q1 2 (r*4+s) = (a s*c)*(b r*c)*q1^(4+4*r+s) := by
  have hi : 16*2+(r*4+s) < 56 := by omega
  have hd : (16*2+(r*4+s))/28 ≠ 0 := by omega
  have hm : (16*2+(r*4+s))%28 = 4+4*r+s := by omega
  simp only [literalCell, hi, if_true, hd, if_false, hm, literalLow_row a b c r s hs]

theorem literalCell_fourth_head (a b : Nat → R) (c q0 q1 : R) (r s : Nat)
    (hr : r < 2) (hs : s < 4) :
    literalCell a b c q0 q1 3 (r*4+s) = (a s*c)*(b r*c)*q1^(20+4*r+s) := by
  have hi : 16*3+(r*4+s) < 56 := by omega
  have hd : (16*3+(r*4+s))/28 ≠ 0 := by omega
  have hm : (16*3+(r*4+s))%28 = 20+4*r+s := by omega
  simp only [literalCell, hi, if_true, hd, if_false, hm, literalLow_row a b c r s hs]

theorem literalCell_fourth_zero (a b : Nat → R) (c q0 q1 : R) (r s : Nat)
    (hr : 2 ≤ r) : literalCell a b c q0 q1 3 (r*4+s) = 0 := by
  have hi : ¬16*3+(r*4+s) < 56 := by omega
  simp only [literalCell, hi, if_false]

theorem literalBlock_rows (a b : Nat → R) (c q0 q1 : R) (j : Nat) :
    literalBlock a b c q0 q1 j =
      sumRange 4 (fun r => sumRange 4 (fun s => literalCell a b c q0 q1 j (r*4+s))) :=
  sumRange_mul 4 4 _

theorem literalBlock_first (a b : Nat → R) (c q0 q1 : R) :
    literalBlock a b c q0 q1 0 = referenceBlock a b c q0 0 [0,1,2,3] := by
  rw [literalBlock_rows]
  change sumRange 4 _ = sumRange 4 _
  apply sumRange_congr
  intro r hr
  apply sumRange_congr
  intro s hs
  exact literalCell_first a b c q0 q1 r s hr hs

theorem literalBlock_second (a b : Nat → R) (c q0 q1 : R) :
    literalBlock a b c q0 q1 1 =
      referenceBlock a b c q0 16 [0,1,2] + secondRunTail a b c q1 := by
  rw [literalBlock_rows, show (4:Nat)=3+1 from rfl, sumRange_add, sumRange_one]
  change sumRange 3 _ + sumRange 4 _ = sumRange 3 _ + sumRange 4 _
  apply congrArg₂ (· + ·)
  · apply sumRange_congr
    intro r hr
    apply sumRange_congr
    intro s hs
    exact literalCell_second_head a b c q0 q1 r s hr hs
  · apply sumRange_congr
    intro s hs
    exact literalCell_second_tail a b c q0 q1 s hs

theorem literalBlock_third (a b : Nat → R) (c q0 q1 : R) :
    literalBlock a b c q0 q1 2 = referenceBlock a b c q1 4 [0,1,2,3] := by
  rw [literalBlock_rows]
  change sumRange 4 _ = sumRange 4 _
  apply sumRange_congr
  intro r hr
  apply sumRange_congr
  intro s hs
  exact literalCell_third a b c q0 q1 r s hr hs

theorem literalBlock_fourth (a b : Nat → R) (c q0 q1 : R) :
    literalBlock a b c q0 q1 3 = referenceBlock a b c q1 20 [0,1] := by
  rw [literalBlock_rows, show (4:Nat)=2+2 from rfl, sumRange_add]
  have hz : sumRange 2 (fun r => sumRange 4 (fun s =>
      literalCell a b c q0 q1 3 ((2+r)*4+s))) = 0 := by
    calc
      _ = sumRange 2 (fun _ => (0 : R)) := by
        apply sumRange_congr
        intro r _
        calc
          _ = sumRange 4 (fun _ => (0 : R)) := by
            apply sumRange_congr
            intro s _
            exact literalCell_fourth_zero a b c q0 q1 (2+r) s (by omega)
          _ = 0 := sumRange_zero 4
      _ = 0 := sumRange_zero 2
  rw [hz, add_zero]
  change sumRange 2 _ = sumRange 2 _
  apply sumRange_congr
  intro r hr
  apply sumRange_congr
  intro s hs
  exact literalCell_fourth_head a b c q0 q1 r s hr hs

theorem literal_eq_cutReference (a b : Nat → R) (c q0 q1 : R) :
    literalWeights a b c q0 q1 = cutReferenceWeights a b c q0 q1 := by
  unfold literalWeights cutReferenceWeights
  rw [literalBlock_first, literalBlock_second, literalBlock_third, literalBlock_fourth]

theorem factored_eq_literal (a b : Nat → R) (c q0 q1 : R) :
    factoredWeights a b c q0 q1 = literalWeights a b c q0 q1 :=
  (factored_eq_cutReference a b c q0 q1).trans (literal_eq_cutReference a b c q0 q1).symm

#print axioms sumRange_mul
#print axioms literalLow_row
#print axioms literal_eq_cutReference
#print axioms factored_eq_literal
end AspisR1.CuSavingsLibra
