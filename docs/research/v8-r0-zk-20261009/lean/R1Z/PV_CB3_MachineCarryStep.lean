import R1Z.PV_CB3_WordMachine
namespace R1Z.PV_CB3_MachineCarryStep
open PV_CB3_SamplerWord
set_option autoImplicit false

def sum (digit addend : BitVec 32) : BitVec 64 := digit.setWidth 64 + addend.setWidth 64

def step (digit addend : BitVec 32) : BitVec 32 × BitVec 32 :=
  ((sum digit addend % PV_CB3_WordMachine.denominator).setWidth 32,
    (sum digit addend / PV_CB3_WordMachine.denominator).setWidth 32)

theorem sum_value (digit addend : BitVec 32) :
    (sum digit addend).toNat = digit.toNat + addend.toNat := by
  have hd := digit.isLt
  have ha := addend.isLt
  dsimp only [sum]
  rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by omega),
    BitVec.toNat_setWidth_of_le (by omega)]
  apply Nat.mod_eq_of_lt
  change digit.toNat + addend.toNat < 18446744073709551616
  change digit.toNat < 4294967296 at hd
  change addend.toNat < 4294967296 at ha
  omega

/-- Both narrowing casts are exact for all pairs of machine words, including
noncanonical digit inputs. No desired-output or range premise is required. -/
theorem projection (digit addend : BitVec 32) :
    (step digit addend).1.toNat = (digit.toNat + addend.toNat) % base ∧
    (step digit addend).2.toNat = (digit.toNat + addend.toNat) / base := by
  have hd := digit.isLt
  have ha := addend.isLt
  have hp : 0 < base := by unfold base; omega
  have hr : (digit.toNat + addend.toNat) % base < 2 ^ 32 := by
    have h := Nat.mod_lt (digit.toNat + addend.toNat) hp
    unfold base at h
    change (digit.toNat + addend.toNat) % base < 4294967296
    omega
  have hq : (digit.toNat + addend.toNat) / base < 2 ^ 32 := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    unfold base
    change digit.toNat < 4294967296 at hd
    change addend.toNat < 4294967296 at ha
    omega
  dsimp only [step]
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_udiv,
    BitVec.toNat_umod, PV_CB3_WordMachine.denominator_value, sum_value,
    Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hq]
  exact ⟨rfl, rfl⟩

#print axioms sum_value
#print axioms projection
end R1Z.PV_CB3_MachineCarryStep
