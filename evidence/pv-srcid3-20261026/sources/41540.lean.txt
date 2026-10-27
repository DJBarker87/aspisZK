import R1Z.PV_Src_ExternalModel
import R0Z.PoseidonCanon
import R0Z.M31Prime

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalCopy
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine

theorem source (state : Array U32 16#usize) :
    PV_Src_ExternalReference.run state =
      R0PoseidonCopy.external_linear state := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨a,ha,hca,hfa⟩ := PV_Src_ExternalModel.source (K := ZMod 2147483647) state
  obtain ⟨b,hb,hfb⟩ := external_lift (K := ZMod 2147483647) state
  have hcb := R0Z.PoseidonRefine.external_canon state b hb
  have he : a=b := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have hj16 : j<16 := by simpa using hj
    have hbl := hfb ⟨j,hj16⟩
    change liftU (K := ZMod 2147483647) b.val[j]! =
      R0P.poseidonExternalLinear (fun i => liftU (K := ZMod 2147483647) state.val[i.val]!) ⟨j,hj16⟩ at hbl
    have hl := (hfa ⟨j,hj16⟩).trans hbl.symm
    unfold liftU at hl
    have hv := congrArg ZMod.val hl
    rw [ZMod.val_natCast,ZMod.val_natCast,
      Nat.mod_eq_of_lt (hca ⟨j,hj16⟩),Nat.mod_eq_of_lt (hcb j hj16)] at hv
    exact UScalar.eq_of_val_eq hv
  rw [ha,hb,he]


#print axioms source
end R1Z.PV_Src_ExternalCopy
