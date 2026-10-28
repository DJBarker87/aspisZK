import R1Z.PV_RunJoin_CompilerSentinel31
import R1Z.PV_RunJoin_SemanticOptions30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticSentinel31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem field_nonzero (n : U32) (hn : n≠0#u32) (bound : n.val<2147483647) : (n.val : K)≠0 := by
  intro h
  have hf : (n.val : F)=0 := by
    apply (ι : F →+* K).injective
    simpa only [map_natCast,map_zero] using h
  have hv := congrArg (fun x : F => x.val) hf
  change (n.val : ZMod 2147483647).val=0 at hv
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt bound] at hv
  exact hn (UScalar.eq_of_val_eq hv)
#print axioms field_nonzero

theorem sentinel (i : Input) (success : run i = ok (.Ok i.compiled))
    (hv : (statement (K := K) i).variant = .privateTransfer) :
    (statement (K := K) i).change 7 ≠ 0 := by
  cases hreq : i.request with
  | withdrawal p =>
    simp only [statement,publicInput,hreq,PV_Src_Public.canonicalPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub] at hv
    cases hv
  | transfer p recipient =>
    have hs := PV_RunJoin_CompilerSentinel31.sentinel i.witness
      (outputValue i.request) (PV_Src_NativeInput.recipient i.request) i.change
      (forestPublic i.request) i.laneAnchor i.snapshot i.compiled p.recipient_commitment
      (by simp only [hreq,forestPublic]) success
    simp only [hreq,forestPublic] at hs
    have hn := field_nonzero (K := K) p.change_commitment.val[7]! hs.2 (hs.1 7 (by decide))
    have lane : (7 : Fin 8).val = 7 := rfl
    simpa only [statement,publicInput,hreq,PV_Src_Public.canonicalPublic,
      BuilderPublicProjection.transferPublic,mapPub,digK,liftU,map_natCast,lane] using hn
#print axioms sentinel
end R1Z.PV_RunJoin_SemanticSentinel31
