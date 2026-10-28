import R1Z.PV_Src_PortInternalModel
import R0Z.PoseidonCanon
import R0Z.M31Prime

/-! Canonical source outputs identify the complete Result with the retained
extracted modulo copy. Field equality is converted back to exact U32 equality. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalCopy
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortInternalStep

theorem shifts_bound : ShiftsBound R0PoseidonCopy.INTERNAL_SHIFTS := by
  intro j hj
  interval_cases j <;> simp only [R0PoseidonCopy.INTERNAL_SHIFTS] <;> decide

theorem shifts_model : ShiftsOk R0PoseidonCopy.INTERNAL_SHIFTS := by
  intro j
  fin_cases j <;> simp only [R0PoseidonCopy.INTERNAL_SHIFTS,R0P.poseidonInternalShifts] <;> rfl

theorem source (state : State) (hs : PV_Src_PortSboxStep.Canonical state) :
    poseidon2.internal_linear_lazy state =
      R0PoseidonCopy.internal_linear state R0PoseidonCopy.INTERNAL_SHIFTS := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨a,ha,hca,hfa⟩ := PV_Src_PortInternalModel.source (K := ZMod 2147483647) state hs
  obtain ⟨b,hb,hfb⟩ := internal_linear_lift (K := ZMod 2147483647)
    state R0PoseidonCopy.INTERNAL_SHIFTS (hs ⟨0,by decide⟩) shifts_bound shifts_model
  have hcb := R0Z.PoseidonRefine.internal_linear_canon state R0PoseidonCopy.INTERNAL_SHIFTS b hb
  have he : a=b := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have hj16 : j<16 := by simpa using hj
    have hbl := hfb ⟨j,hj16⟩
    change liftU (K := ZMod 2147483647) b.val[j]! =
      R0P.poseidonInternalLinear (fun i => liftU (K := ZMod 2147483647) state.val[i.val]!) ⟨j,hj16⟩ at hbl
    have hl := (hfa ⟨j,hj16⟩).trans hbl.symm
    unfold liftU at hl
    have hv := congrArg ZMod.val hl
    rw [ZMod.val_natCast,ZMod.val_natCast,
      Nat.mod_eq_of_lt (hca ⟨j,hj16⟩),Nat.mod_eq_of_lt (hcb j hj16)] at hv
    exact UScalar.eq_of_val_eq hv
  rw [ha,hb,he]

#print axioms shifts_bound
#print axioms shifts_model
#print axioms source
end R1Z.PV_Src_PortInternalCopy
