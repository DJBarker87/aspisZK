import R1Z.PV_RunJoin_ConsumerBoundary25
set_option autoImplicit false
noncomputable section
namespace PV_L2C_HonestCaller
open R1Z R0P R0Z.ZkStatement R0Z.HonestValidity
open PV_Src_NativeInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Exactly the lead's honest carrier; no guard result is added. -/
abbrev Family := {i : Input // PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K) i}

def inputs (i : Family (K:=K)) : Input := i.val
abbrev source := PV_Src_NativeIdentification.prover (K:=K) inputs PV_Src_Transport.transport

def target : Family (K:=K) → BuilderCanonical.Instance (K:=K) :=
  PV_RunJoin_UniversalBuild22.toInstance inputs (fun i => i.property.1)

/-- Universal caller transport through the actual returned compiler payload.
The compiler-success, Checked and frontier facts are projected from honesty. -/
theorem identification : BuilderSource.SourceIdentification (source (K:=K)) target :=
  PV_RunJoin_UniversalBuild22.identification inputs (fun i => i.property.1)
    (fun i => i.property.2.1) (fun i => i.property.2.2.1) (fun i => i.property.2.2.2)
#print axioms identification

/-- The guard caller's cached columns are the bank actually returned on this input. -/
theorem returned_bank (i : Family (K:=K)) :
    ∃ banks, BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.CopyRecords.banks
        (PV_RunJoin_UniversalBuild22.records i.val) = Aeneas.Result.ok (some banks) ∧
      i.val.compiled.semantic_c1.c1 = banks.merged :=
  PV_RunJoin_UniversalBuild22.returned_bank i.val i.property.2.1
#print axioms returned_bank

theorem field_large : 4096 < Fintype.card K := by
  have hc : Fintype.card (ZMod AspisCircleGroupOrder.P) ≤ Fintype.card K :=
    Fintype.card_le_of_injective (algebraMap (ZMod AspisCircleGroupOrder.P) K)
      (RingHom.injective _)
  rw [ZMod.card] at hc
  have hp : AspisCircleGroupOrder.P = 2147483647 := rfl
  rw [hp] at hc
  omega
#print axioms field_large

/-- Soundness of the decoded raw trace for every input in precisely Family.
This does not assert canonicality of the native U32 representation. -/
theorem builder_sound {CommitHandle : Type} (F : Subfield K)
    (B : PackBasis F) (x : Statement K CommitHandle) :
    BuilderSoundOn (source (K:=K)) B x :=
  BuilderSource.builder_refinement_D46_D51 field_large F B x source target identification
#print axioms builder_sound

theorem transfer : PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K)
    PV_RunJoin_AdmittedCarrier23.transfer := PV_RunJoin_ConsumerBoundary25.transfer_honest
#print axioms transfer

theorem withdrawal : PV_RunJoin_ConsumerBoundary25.HonestInput (K:=K)
    PV_RunJoin_AdmittedCarrier23.withdrawal := PV_RunJoin_ConsumerBoundary25.withdrawal_honest
#print axioms withdrawal
end PV_L2C_HonestCaller
