import R1Z.PV_Src_PortField
set_option autoImplicit false
namespace R1Z.PV_Src_PortNodeTweak
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderForestAdmissionPort
variable {K : Type} [Field K] [CharP K 2147483647]

theorem constant : liftU (K := K) poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK = -(1051521018 : K) := by
  simp only [liftU,poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK,UScalar.ofNatCore_val_eq]
  change (1095962629 : K) = -(1051521018 : K)
  have h : (1095962629 : K) + 1051521018 = 0 := by
    calc
      _ = (2147483647 : K) := by norm_num
      _ = 0 := CharP.cast_eq_zero K 2147483647
  exact eq_neg_of_add_eq_zero_left h

theorem source (x : U32) (hx : x.val < 2147483647) :
    ∃ z, aspis_core.field.M31.add x poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK = ok z ∧
      z.val < 2147483647 ∧ liftU (K := K) z = liftU x - (1051521018 : K) := by
  obtain ⟨z,hz,hc,hm⟩ := PV_Src_PortField.addition (K := K) x
    poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK hx (by
      simp only [poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK,UScalar.ofNatCore_val_eq];decide)
  refine ⟨z,hz,hc,?_⟩
  rw [hm,constant,sub_eq_add_neg]

#print axioms constant
#print axioms source
end R1Z.PV_Src_PortNodeTweak
