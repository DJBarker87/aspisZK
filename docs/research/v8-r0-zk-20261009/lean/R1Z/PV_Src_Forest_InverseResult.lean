/- Namespace port of BuilderInverseResult: same symbolic proof, actual forest extraction. -/
import R1Z.PV_Src_Forest_Inverse

/-! Apply the checked symbolic exponentiation invariant at the shipped
exponent. Large powers remain symbolic through the scalar word conversion. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Forest_InverseResult
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem inverse (x : U32) : inv_r x = ok (invR x) := by
  have hc : (UScalar.cast .U64 x).val = x.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have hx : x.val < 2^32 := x.hBounds
    simp only [UScalarTy.numBits]
    omega
  obtain ⟨b,hb,hbv⟩ := WP.spec_imp_exists (UScalar.rem_spec (UScalar.cast .U64 x)
    (y := 2147483647#u64) (by decide))
  have hbv' : b.val = x.val % 2147483647 := by simpa only [hc,UScalar.ofNatCore_val_eq] using hbv
  obtain ⟨out,hout,ho,hval⟩ := PV_Src_Forest_Inverse.loop
    b 2147483645#u64 1#u64 (by rw [hbv']; exact Nat.mod_lt _ (by decide)) (by decide)
  have ho' : out.val < 2147483647 := ho
  have hfield : (out.val : ZMod 2147483647) = (b.val : ZMod 2147483647)^2147483645 := by
    have hv : (out.val : ZMod 2147483647) = (1 : ZMod 2147483647) * (b.val : ZMod 2147483647)^2147483645 := hval
    simpa only [one_mul] using hv
  have houtval := PV_Src_Forest_Inverse.field_power_value b out x.val 2147483645 hbv' ho' hfield
  have hword : UScalar.cast .U32 out = invR x := by
    apply UScalar.eq_of_val_eq
    exact PV_Src_Forest_Inverse.cast_word_value out (x.val^2147483645) houtval
  unfold inv_r
  simp only [BuilderForestAdmissionPort.aspis_core.field.P,lift,bind_tc_ok]
  change (do let b ← (UScalar.cast .U64 x % 2147483647#u64 : Result U64)
             let out ← inv_r_loop b 2147483645#u64 1#u64
             ok (UScalar.cast .U32 out)) = _
  rw [hb]
  simp only [bind_tc_ok]
  rw [hout]
  simp only [bind_tc_ok,hword]

#print axioms inverse
end R1Z.PV_Src_Forest_InverseResult
