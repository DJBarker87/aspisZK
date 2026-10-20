import R17ActualA00IndexPower
import R17ActualA01IndexPower
import R17ActualA02IndexPower
import R17ActualA03IndexPower
import R17ActualA04IndexPower
import R17ActualA05IndexPower
import R17ActualA06IndexPower
import R17ActualA07IndexPower
import R17ActualA08IndexPower
import R17ActualA09IndexPower
import R17ActualA10IndexPower
import R17ActualA11IndexPower
import R17ActualA12IndexPower
import R17ActualA13IndexPower
import R17ActualA14IndexPower
import R17ActualA15IndexPower
import R17ActualB00IndexPower
import R17ActualB01IndexPower
import R17ActualB02IndexPower
import R17ActualB03IndexPower
import R17ActualB04IndexPower
import R17ActualB05IndexPower
import R17ActualB06IndexPower
import R17ActualB07IndexPower
import R17ActualB08IndexPower
import R17ActualB09IndexPower
import R17ActualB10IndexPower
import R17ActualB11IndexPower
import R17ActualB12IndexPower
import R17ActualB13IndexPower
import R17ActualB14IndexPower
import R17ActualB15IndexPower
import R17ActualTableArrayIndexV1
import R17TableExponentDomainBridge
import R17ZPowAddition
import Aeneas
import Lean.Elab.Tactic.Omega

open Aeneas Aeneas.Std
set_option autoImplicit false

namespace R17ActualWholeTablePower
open AspisR1QueryGeometryActual R17TableBasePowerBridge R17TableExponentDomainBridge

theorem actual_table_a_index_power (i : Usize) (hi : i.val < 512) :
    ∀ p, Array.index_usize fast_domain.TABLE_A i = .ok p →
      decode (R17TableAChunk00Certificate.toNatC (⟨p.1.val, p.2.val⟩ : R17TableBasePowerProbe.C)) =
        zPow (decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen)) (leftExponent i.val) := by
  intro p hget
  let q : Nat := i.val / 32
  let j : Nat := i.val % 32
  have hq : q < 16 := by dsimp [q]; omega
  have hj : j < 32 := by dsimp [j]; omega
  have hsplit : i.val = 32 * q + j := by dsimp [q, j]; omega
  have hqcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 := by omega
  rcases hqcases with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
  ·
    rw [hq] at hsplit
    have hp := R17ActualA00IndexPower.actual_table_a00_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk00Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA01IndexPower.actual_table_a01_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk01Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA02IndexPower.actual_table_a02_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk02Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA03IndexPower.actual_table_a03_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk03Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA04IndexPower.actual_table_a04_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk04Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA05IndexPower.actual_table_a05_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk05Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA06IndexPower.actual_table_a06_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk06Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA07IndexPower.actual_table_a07_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk07Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA08IndexPower.actual_table_a08_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk08Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA09IndexPower.actual_table_a09_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk09Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA10IndexPower.actual_table_a10_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk10Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA11IndexPower.actual_table_a11_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk11Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA12IndexPower.actual_table_a12_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk12Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA13IndexPower.actual_table_a13_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk13Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA14IndexPower.actual_table_a14_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk14Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualA15IndexPower.actual_table_a15_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableAChunk15Certificate.toNatC, R17TableAChunk00Certificate.toNatC] using hp
#print axioms actual_table_a_index_power

theorem actual_table_b_index_power (i : Usize) (hi : i.val < 512) :
    ∀ p, Array.index_usize fast_domain.TABLE_B i = .ok p →
      decode (R17TableBChunk00Certificate.toNatC (⟨p.1.val, p.2.val⟩ : R17TableBasePowerProbe.C)) =
        zPow (decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen)) (rightExponent i.val) := by
  intro p hget
  let q : Nat := i.val / 32
  let j : Nat := i.val % 32
  have hq : q < 16 := by dsimp [q]; omega
  have hj : j < 32 := by dsimp [j]; omega
  have hsplit : i.val = 32 * q + j := by dsimp [q, j]; omega
  have hqcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 := by omega
  rcases hqcases with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
  ·
    rw [hq] at hsplit
    have hp := R17ActualB00IndexPower.actual_table_b00_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk00Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB01IndexPower.actual_table_b01_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk01Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB02IndexPower.actual_table_b02_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk02Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB03IndexPower.actual_table_b03_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk03Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB04IndexPower.actual_table_b04_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk04Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB05IndexPower.actual_table_b05_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk05Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB06IndexPower.actual_table_b06_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk06Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB07IndexPower.actual_table_b07_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk07Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB08IndexPower.actual_table_b08_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk08Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB09IndexPower.actual_table_b09_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk09Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB10IndexPower.actual_table_b10_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk10Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB11IndexPower.actual_table_b11_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk11Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB12IndexPower.actual_table_b12_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk12Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB13IndexPower.actual_table_b13_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk13Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB14IndexPower.actual_table_b14_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk14Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
  ·
    rw [hq] at hsplit
    have hp := R17ActualB15IndexPower.actual_table_b15_index_power j hj i hsplit p hget
    rw [← hsplit] at hp
    simpa [R17TableBChunk15Certificate.toNatC, R17TableBChunk00Certificate.toNatC] using hp
#print axioms actual_table_b_index_power

theorem actual_table_pair_product (ia ib : Usize) (hia : ia.val < 512) (hib : ib.val < 512)
    (pa pb : Std.U32 × Std.U32)
    (ha : Array.index_usize fast_domain.TABLE_A ia = .ok pa)
    (hb : Array.index_usize fast_domain.TABLE_B ib = .ok pb) :
    zMul
      (decode (R17TableAChunk00Certificate.toNatC (⟨pa.1.val, pa.2.val⟩ : R17TableBasePowerProbe.C)))
      (decode (R17TableBChunk00Certificate.toNatC (⟨pb.1.val, pb.2.val⟩ : R17TableBasePowerProbe.C))) =
    zPow (decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
      (2 ^ 10 + 2 ^ 12 *
        AspisV5FriBitReverse.reverseBits 18 (2 ^ 9 * ib.val + ia.val)) := by
  have hA := actual_table_a_index_power ia hia pa ha
  have hB := actual_table_b_index_power ib hib pb hb
  have hsum := pairedTableExponent_eq_stored ia.val ib.val (by omega) (by omega)
  calc
    zMul (decode (R17TableAChunk00Certificate.toNatC (⟨pa.1.val, pa.2.val⟩ : R17TableBasePowerProbe.C)))
        (decode (R17TableBChunk00Certificate.toNatC (⟨pb.1.val, pb.2.val⟩ : R17TableBasePowerProbe.C))) =
      zMul (zPow (decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (leftExponent ia.val))
        (zPow (decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (rightExponent ib.val)) := by rw [hA, hB]; rfl
    _ = zPow (decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (leftExponent ia.val + rightExponent ib.val) := by
          symm; exact R17ZPowAddition.zPow_add _ _ _
    _ = zPow (decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (2 ^ 10 + 2 ^ 12 * AspisV5FriBitReverse.reverseBits 18 (2 ^ 9 * ib.val + ia.val)) := by rw [hsum]

#print axioms actual_table_pair_product

end R17ActualWholeTablePower
