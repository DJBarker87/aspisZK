import S9ActualEbyKBackendTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualEbyKCountSourceV1
open AspisR1S9ActualEbyKBackendTransportV1

/-- Both source implementations read the same eight value coordinates. -/
theorem native_from_wide_source (w : NativeW) :
    fast_pairing.canonical.Q.from_wide w = AspisR1EbyKPushWideToQ.fromWide (toSourceWide w) := by
  rfl

/-- The actual4096-term guard makes checked and wrapping increments identical,
without an additional count or architecture assumption. -/
theorem checked_count_add_eq_wrapping (n : Usize) (hn : n < fast_pairing.MAX_TERMS) :
    UScalar.add n 1#usize = .ok (Usize.wrapping_add n 1#usize) := by
  unfold fast_pairing.MAX_TERMS at hn
  have hnval : n.val < 4096 := by simpa using hn
  have hmax : 4096 ≤ Usize.max := by scalar_tac
  have hroom : n.val + 1 ≤ Usize.max := by omega
  have haddSpec : UScalar.add n 1#usize ⦃ z => z.val=n.val+1 ⦄ := by
    apply UScalar.add_spec
    have hsum : n.val+(1#usize).val ≤ Usize.max := by simpa using hroom
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨i,hi,hval⟩ := WP.spec_imp_exists haddSpec
  have hsize : 4096 < UScalar.size .Usize := by scalar_tac
  have hwrapped : (Usize.wrapping_add n 1#usize).val=n.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    change (n.val+1) % UScalar.size .Usize=n.val+1
    exact Nat.mod_eq_of_lt (by omega)
  have he : i=Usize.wrapping_add n 1#usize := UScalar.eq_of_val_eq (hval.trans hwrapped.symm)
  exact he ▸ hi

#print axioms native_from_wide_source
#print axioms checked_count_add_eq_wrapping
end AspisR1S9ActualEbyKCountSourceV1
