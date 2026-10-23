import S9ActualRawNativeOperandsV1
import S9ActualRawHookIdentityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualRawNativeHookV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9ActualRawNativeOperandsV1
/-- On the SAME current native fromWide/checked_q operands, the actual
unmodified Rust raw body agrees with the externally installed raw model.
The model alias identity is explicit; it is not substituted for source
refinement. Canonical-domain source equality was proved separately. -/
theorem actual_same_operands_raw_hook (w : NativeW) (scalar : NativeQ) (q : A4)
    (hw : w.c0.c0.a.val ≤ 2^31-2 ∧ w.c0.c0.b.val ≤ 2^31-2 ∧
      w.c0.c1.a.val ≤ 2^31-2 ∧ w.c0.c1.b.val ≤ 2^31-2 ∧
      w.c1.c0.a.val ≤ 2^31-2 ∧ w.c1.c0.b.val ≤ 2^31-2 ∧
      w.c1.c1.a.val ≤ 2^31-2 ∧ w.c1.c1.b.val ≤ 2^31-2)
    (hchecked : fast_pairing.checked_q scalar = .ok (.Ok q)) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw (low w) q =
      AspisR1S9ActualDotBackendMapV1.actualRaw (low w) q ∧
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw (high w) q =
      AspisR1S9ActualDotBackendMapV1.actualRaw (high w) q := by
  obtain ⟨_,hlo,hhi⟩ := actual_same_operands_raw_refines w scalar q hw hchecked
  have hmodelLo := AspisR1S9ActualRawHookIdentityV1.actual_raw_eq_source (low w) q
  have hmodelHi := AspisR1S9ActualRawHookIdentityV1.actual_raw_eq_source (high w) q
  change AspisR1S9ActualDotBackendMapV1.actualRaw (low w) q =
    AspisR1CanonicalQRawUnified.canonical.Q.raw (low w) q at hmodelLo
  change AspisR1S9ActualDotBackendMapV1.actualRaw (high w) q =
    AspisR1CanonicalQRawUnified.canonical.Q.raw (high w) q at hmodelHi
  exact ⟨hlo.trans hmodelLo.symm,hhi.trans hmodelHi.symm⟩
#print axioms actual_same_operands_raw_hook
end AspisR1S9ActualRawNativeHookV1
