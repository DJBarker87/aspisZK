import GammaCandidateLowQuotient
import ExtractedQM31SamplerPass
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace LPk_Step
open AspisR1.SamplerMachineBounds AspisR1.SamplerWord

/-- Natural relation checked for a native step. No division equivalence is
assumed by callers of the stub. -/
def Relation (rem limb q r : Nat) : Prop :=
  q * P + r = rem * B + limb ∧ r < P

theorem unique (rem limb q r : Nat) (h : Relation rem limb q r) :
    q = (rem * B + limb) / P ∧ r = (rem * B + limb) % P := by
  obtain ⟨he,hr⟩ := h
  have hq : (rem * B + limb) / P = q := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [← he, Nat.add_mul, one_mul]
      omega
  refine ⟨hq.symm, ?_⟩
  have hm := Nat.mod_add_div (rem * B + limb) P
  rw [hq, Nat.mul_comm P q] at hm
  omega

/-- Pairing theorem for the step stub, on the complete native domain. -/
theorem machine_step (rem : UInt64) (limb : UInt32) (hr : rem.toNat < P) :
    Relation rem.toNat limb.toNat (machineStep rem limb).1.toNat
      (machineStep rem limb).2.toNat := by
  rw [Relation, machineStep_quotient_toNat limb hr, machineStep_remainder_toNat limb hr]
  exact ⟨by simpa only [B, Nat.mul_comm, Nat.add_comm] using
    Nat.mod_add_div (rem.toNat * 2^32 + limb.toNat) P,
    Nat.mod_lt _ P_pos⟩

theorem step_join (rem : UInt64) (limb q r : UInt32)
    (hr : rem.toNat < P) (h : Relation rem.toNat limb.toNat q.toNat r.toNat) :
    (q,r) = machineStep rem limb := by
  have hu := unique _ _ _ _ h
  apply Prod.ext <;> apply UInt32.toNat.inj
  · exact hu.1.trans (machineStep_quotient_toNat limb hr).symm
  · exact hu.2.trans (machineStep_remainder_toNat limb hr).symm
#print axioms unique
#print axioms machine_step
#print axioms step_join
end LPk_Step
