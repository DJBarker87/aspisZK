import R1SamplerWord
import R1SamplerPass
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AspisR1.SamplerWordPass

open AspisR1.SamplerMachineBounds AspisR1.SamplerWord AspisR1.SamplerPass

def machineProcess (r : UInt64) : List UInt32 → UInt64 × List UInt32
  | [] => (r, [])
  | d :: digits =>
      let step := machineStep r d
      let tail := machineProcess (UInt64.ofNat step.2.toNat) digits
      (tail.1, step.1 :: tail.2)

theorem machineProcess_length (r : UInt64) (digits : List UInt32) :
    (machineProcess r digits).2.length = digits.length := by
  induction digits generalizing r with
  | nil => rfl
  | cons digit digits ih => simp [machineProcess, ih]

theorem uint32_to_uint64_toNat (d : UInt32) :
    (UInt64.ofNat d.toNat).toNat = d.toNat := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  exact lt_trans (UInt32.toNat_lt d) (by norm_num)

theorem foldl_numeral (radix accumulator : Nat) (digits : List Nat) :
    digits.foldl (fun a d => a * radix + d) accumulator =
      accumulator * radix ^ digits.length + numeral radix digits := by
  induction digits generalizing accumulator with
  | nil => simp [numeral]
  | cons digit digits ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (accumulator * radix + digit)]
      have hcons : numeral radix (digit :: digits) =
          digits.foldl (fun a d => a * radix + d) digit := by
        simp [numeral, List.foldl_cons]
      rw [hcons, ih digit, Nat.pow_succ]
      ring

theorem numeral_cons (radix digit : Nat) (digits : List Nat) :
    numeral radix (digit :: digits) =
      digit * radix ^ digits.length + numeral radix digits := by
  change digits.foldl (fun a d => a * radix + d) (0 * radix + digit) = _
  simp only [Nat.zero_mul, Nat.zero_add]
  exact foldl_numeral radix digit digits

theorem machineProcess_correct (r : UInt64) (digits : List UInt32)
    (hr : r.toNat < P) :
    let output := machineProcess r digits
    output.1.toNat =
        (r.toNat * B ^ digits.length + numeral B (digits.map UInt32.toNat)) % P ∧
      numeral B (output.2.map UInt32.toNat) =
        (r.toNat * B ^ digits.length + numeral B (digits.map UInt32.toNat)) / P := by
  induction digits generalizing r with
  | nil =>
      simp [machineProcess, numeral, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr]
  | cons digit digits ih =>
      let step := machineStep r digit
      let next := UInt64.ofNat step.2.toNat
      have hquot := machineStep_quotient_toNat digit hr
      have hrem := machineStep_remainder_toNat digit hr
      have hnext : next.toNat = step.2.toNat := uint32_to_uint64_toNat step.2
      have hnext_lt : next.toNat < P := by
        rw [hnext, hrem]
        exact Nat.mod_lt _ P_pos
      have htail := ih next hnext_lt
      change
        (machineProcess next digits).1.toNat =
            (r.toNat * B ^ (digits.length + 1) +
              numeral B ((digit :: digits).map UInt32.toNat)) % P ∧
          numeral B ((step.1.toNat ::
              (machineProcess next digits).2.map UInt32.toNat)) =
            (r.toNat * B ^ (digits.length + 1) +
              numeral B ((digit :: digits).map UInt32.toNat)) / P
      let chunk := r.toNat * B + digit.toNat
      let tailInput := step.2.toNat * B ^ digits.length +
        numeral B (digits.map UInt32.toNat)
      let total := r.toNat * B ^ (digits.length + 1) +
        numeral B ((digit :: digits).map UInt32.toNat)
      have htotal : total = chunk * B ^ digits.length +
          numeral B (digits.map UInt32.toNat) := by
        dsimp [total, chunk]
        rw [numeral_cons, List.length_map, Nat.pow_succ]
        ring
      have hquotChunk : step.1.toNat = chunk / P := by
        simpa [chunk, B] using hquot
      have hremChunk : step.2.toNat = chunk % P := by
        simpa [chunk, B] using hrem
      have hchunk : chunk = P * step.1.toNat + step.2.toNat := by
        rw [hquotChunk, hremChunk]
        simpa [Nat.add_comm] using (Nat.mod_add_div chunk P).symm
      have htailR : (machineProcess next digits).1.toNat = tailInput % P := by
        simpa [tailInput, hnext] using htail.1
      have htailQ : numeral B ((machineProcess next digits).2.map UInt32.toNat) =
          tailInput / P := by
        simpa [tailInput, hnext] using htail.2
      have htailDiv : tailInput = P * (tailInput / P) + tailInput % P := by
        simpa [Nat.add_comm] using (Nat.mod_add_div tailInput P).symm
      have htotalDiv : total = P *
          (step.1.toNat * B ^ digits.length + tailInput / P) + tailInput % P := by
        rw [htotal, hchunk]
        calc
          (P * step.1.toNat + step.2.toNat) * B ^ digits.length +
              numeral B (digits.map UInt32.toNat) =
              P * (step.1.toNat * B ^ digits.length) + tailInput := by
                dsimp [tailInput]
                ring
          _ = P * (step.1.toNat * B ^ digits.length) +
              (P * (tailInput / P) + tailInput % P) := by
                exact congrArg (fun t => P * (step.1.toNat * B ^ digits.length) + t)
                  htailDiv
          _ = P * (step.1.toNat * B ^ digits.length + tailInput / P) +
              tailInput % P := by ring
      have hremBound : tailInput % P < P := Nat.mod_lt _ P_pos
      let totalQuotient := step.1.toNat * B ^ digits.length + tailInput / P
      have hquotTotal : total / P = totalQuotient := by
        apply Nat.div_eq_of_lt_le
        · rw [htotalDiv]
          calc
            totalQuotient * P = P * totalQuotient := Nat.mul_comm _ _
            _ ≤ P * totalQuotient + tailInput % P := Nat.le_add_right _ _
        · rw [htotalDiv]
          calc
            P * totalQuotient + tailInput % P <
                P * totalQuotient + P := Nat.add_lt_add_left hremBound _
            _ = (totalQuotient + 1) * P := by
                rw [Nat.add_mul, one_mul, Nat.mul_comm totalQuotient P]
      have hmodTotal : total % P = tailInput % P := by
        have hdivEq : total % P + P * totalQuotient = total := by
          simpa [hquotTotal] using (Nat.mod_add_div total P)
        calc
          total % P = (total % P + P * totalQuotient) - P * totalQuotient := by omega
          _ = total - P * totalQuotient :=
            congrArg (fun z => z - P * totalQuotient) hdivEq
          _ = (P * totalQuotient + tailInput % P) - P * totalQuotient := by
            rw [htotalDiv]
          _ = tailInput % P := by omega
      constructor
      · rw [htailR, hmodTotal]
      · rw [numeral_cons]
        simp only [List.length_map, machineProcess_length]
        rw [htailQ, hquotTotal]

#print axioms uint32_to_uint64_toNat
#print axioms foldl_numeral
#print axioms numeral_cons
#print axioms machineProcess_length
#print axioms machineProcess_correct

end AspisR1.SamplerWordPass
