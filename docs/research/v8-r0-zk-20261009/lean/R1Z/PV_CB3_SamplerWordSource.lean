-- Exact generated scalar definitions; generated resource overrides removed.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CB3_ShippedOp249word

/-- [aspis_core::field::P]
    Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [pv_cb3_kani::reference_split::word_step]:
    Source: 'reference_split.rs', lines 15:0-18:1
    Visibility: public -/
def reference_split.word_step
  (word : Std.U32) (remainder : Std.U64) : Result (Std.U32 × Std.U64) := do
  let i ← lift (Std.U64.wrapping_shl remainder 32#u32)
  let i1 ← lift (core.convert.num.FromU64U32.from word)
  let dividend ← lift (i ||| i1)
  let i2 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i3 ← dividend / i2
  let i4 ← lift (UScalar.cast .U32 i3)
  let i5 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i6 ← dividend % i5
  ok (i4, i6)

end PV_CB3_ShippedOp249word

namespace R1Z.PV_CB3_SamplerWordSource
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev denominator : U64 :=
  core.convert.num.FromU64U32.from PV_CB3_ShippedOp249word.aspis_core.field.P
abbrev dividend (word : U32) (prior : U64) : U64 :=
  (U64.wrapping_shl prior 32#u32) ||| (core.convert.num.FromU64U32.from word)

theorem denominator_nonzero : denominator.val ≠ 0 := by
  rw [core.convert.num.FromU64U32.from_val_eq]
  unfold PV_CB3_ShippedOp249word.aspis_core.field.P
  change (2147483647 : Nat) ≠ 0
  omega

/-- The complete generated Result, with actual intermediate quotient/remainder
specifications derived from the standard unsigned scalar model. -/
theorem word_total_spec (word : U32) (prior : U64) :
    ∃ (quotient remainder : U64),
      PV_CB3_ShippedOp249word.reference_split.word_step word prior =
        ok (UScalar.cast .U32 quotient, remainder) ∧
      quotient.val = (dividend word prior).val / denominator.val ∧
      remainder.val = (dividend word prior).val % denominator.val := by
  obtain ⟨q,hq,hqv⟩ := UScalar.div_spec (dividend word prior) denominator_nonzero
  obtain ⟨r,hr,hrv⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (dividend word prior) denominator_nonzero)
  refine ⟨q,r,?_,hqv,hrv⟩
  simp only [PV_CB3_ShippedOp249word.reference_split.word_step,lift,bind_tc_ok]
  change (do let q ← dividend word prior / denominator
             let r ← dividend word prior % denominator
             ok (UScalar.cast .U32 q,r)) = _
  rw [hq]
  simp only [bind_tc_ok,hr]

theorem word_total (word : U32) (prior : U64) :
    ∃ q r, PV_CB3_ShippedOp249word.reference_split.word_step word prior = ok (q,r) := by
  obtain ⟨q,r,h,_,_⟩ := word_total_spec word prior
  exact ⟨_,_,h⟩
#print axioms denominator_nonzero
#print axioms word_total_spec
#print axioms word_total
end R1Z.PV_CB3_SamplerWordSource
