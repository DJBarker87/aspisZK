import SAQ_CompleteTop
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Nonvacuity
open Aeneas Aeneas.Std Result

theorem contracts {F C : Type} (indexError : C) (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    Port5Q1_QueryPorts.SessionAPrimitives (SAQ_CompleteInstall.configuration indexError c reservation).query ∧
    Port5Q1_GeometryCanonical.SessionAPrimitives (SAQ_CompleteInstall.configuration indexError c reservation).geometry ∧
    Port5Q1_Domain.SessionADomain (SAQ_CompleteInstall.configuration indexError c reservation).geometry :=
  ⟨SAQ_CompleteInstall.primitives indexError c reservation,
    SAQ_Constructor.canonical indexError c.geometry,SAQ_Constructor.domain indexError c.geometry⟩

theorem constructor_partition {C : Type} (indexError : C) :
    SAQ_Constructor.fibre indexError 0#usize=ok (.Ok 0#usize) ∧
    SAQ_Constructor.fibre indexError 262144#usize=ok (.Err indexError) := by
  constructor <;> rfl

theorem inverse_success : SAQ_Inverse.source 1#u32=ok 1#u32 := by
  obtain ⟨z,run,value⟩ := AspisR1M31Inverse.SquareProof.current_inv_total_power (1#u32) (by decide)
  have hc := AspisR1M31Inverse.SquareProof.current_inv_success_canonical (1#u32) z run
  have sem : S7JoinBasisMachine.decode z=S7JoinBasisMachine.decode (1#u32) := by
    simpa [R17CurrentM31Semantics.decode,S7JoinBasisMachine.decode] using value
  have same := SAQ_Inverse.canonical_injective z (1#u32) hc (by change (1:Nat)<2147483647; decide) sem
  exact run.trans (congrArg Result.ok same)

#print axioms contracts
#print axioms constructor_partition
#print axioms inverse_success
end AspisR1.SAQ_Nonvacuity
end
