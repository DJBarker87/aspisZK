import LPk_Cohort
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace LPk_Induction
open AspisR1.SamplerMachineBounds AspisR1.SamplerWord AspisR1.SamplerWordPass
open AspisR1.SamplerRepeatedPass AspisR1.SourceSamplerByteRank

/-- An execution trace of native high-to-low limb steps, specified only by
the relation checked by Kani. The list order is supplied by the traversal gate. -/
inductive Pass : UInt64 → List UInt32 → UInt64 → List UInt32 → Prop where
  | nil (r : UInt64) : Pass r [] r []
  | cons {r : UInt64} {d q : UInt32} {r1 r2 : UInt64} {ds qs : List UInt32}
      (step : LPk_Step.Relation r.toNat d.toNat q.toNat r1.toNat)
      (tail : Pass r1 ds r2 qs) : Pass r (d::ds) r2 (q::qs)

theorem pass_join {r out : UInt64} {xs qs : List UInt32}
    (trace : Pass r xs out qs) (hr : r.toNat < P) :
    (out,qs) = machineProcess r xs := by
  induction trace with
  | nil r => rfl
  | @cons r d q r1 r2 ds qs hs ht ih =>
    have hu := LPk_Step.unique _ _ _ _ hs
    have hq : q = (machineStep r d).1 := UInt32.toNat.inj
      (hu.1.trans (machineStep_quotient_toNat d hr).symm)
    have hre : r1 = UInt64.ofNat (machineStep r d).2.toNat := by
      apply UInt64.toNat.inj
      rw [uint32_to_uint64_toNat]
      exact hu.2.trans (machineStep_remainder_toNat d hr).symm
    have hi := ih hs.2
    simp only [machineProcess]
    rw [←hq, ←hre, ←hi]

/-- Eight ordered shared-capture callbacks compose eight division passes.
The native from_fn gate supplies this order; this is not an assumption of
whole-function equality. -/
inductive Digits : Nat → List UInt32 → List Nat → List UInt32 → Prop where
  | nil (xs : List UInt32) : Digits 0 xs [] xs
  | cons {n : Nat} {xs qs out : List UInt32} {r : UInt64} {ds : List Nat}
      (pass : Pass 0 xs r qs) (tail : Digits n qs ds out) :
      Digits (n+1) xs (r.toNat::ds) out

theorem digits_join {n : Nat} {xs out : List UInt32} {ds : List Nat}
    (trace : Digits n xs ds out) : (ds,out) = run n xs := by
  induction trace with
  | nil xs => rfl
  | @cons n xs qs out r ds hp ht ih =>
    have he := pass_join hp (show (0 : UInt64).toNat < P from P_pos)
    simp only [run]
    rw [←he, ←ih]

theorem eight_digits {block : Array U8 32#usize} {out : List UInt32} {ds : List Nat}
    (trace : Digits 8 (AspisR1.SamplerBytePass.digits block) ds out) :
    ds = AspisR1.SamplerNatModel.ordinaryDigits (rank block) ∧
    wordValue out = rank block / P^8 ∧ wordValue out ≤ 256 := by
  have he := digits_join trace
  have hd := congrArg Prod.fst he
  have ho := congrArg Prod.snd he
  refine ⟨hd.trans (run8_bytes block), ?_, ?_⟩
  · rw [ho]; exact remaining8_value block
  · rw [ho, remaining8_value]; exact rank_div_P8_le_256 (rank_lt block)
#print axioms pass_join
#print axioms digits_join
#print axioms eight_digits
end LPk_Induction
