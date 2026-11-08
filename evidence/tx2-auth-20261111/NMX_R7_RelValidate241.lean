import NMX_R7_RelReads241
import NMS_R2Facts242
set_option autoImplicit false
namespace NMX_R7_RelValidate241
open NMX_R7_RelVerify241
open RSL RSL.TX2_241 NMS_R2Refine NMS_R2StepFacts NMS_R2Replay241
/-- Precisely the successful 242 guarantees needed at its caller. These are
derived from the whole child packet, not extra parent-input clauses. -/
def ValidatedScope (L : PoolLib) (a : Args) (validated : TX2_242.Validated L) : Prop :=
 validated.proof_length = PROOF_BYTES ∧ a.accounts.length = 7 ∧
 ∃ v, a.accounts[6]? = some v ∧ v.length = .ok CHECKPOINT_BYTES

theorem fold (L : PoolLib) (V : V2Lib) (verify : VerifyRelation V)
 (packet : RelPacket V verify) (a : Args) (domain : Domain V a)
 (validated : TX2_242.Validated L) (scope : ValidatedScope L a validated) :
 Refines (afterValidate L V verify a validated)
  (afterValidate L V (modelVerify V) a validated) := by
 unfold afterValidate
 apply rsbind_using (refl _)
 intro env acc0 events hindex
 have index0 := index_return _ _ env acc0 events hindex
 apply (rsbind_using (refl _) ?_) env
 intro env' proofData events' hread
 have read0 := NMS_R2Getters.success _ env' proofData events' hread
 apply (rsbind_using (refl _) ?_) env'
 intro env'' acc6 events'' hindex6
 have index6 := index_return _ _ env'' acc6 events'' hindex6
 apply (rsbind_using (refl _) ?_) env''
 intro env''' checkpointData events''' hread6
 have read6 := NMS_R2Getters.success _ env''' checkpointData events''' hread6
 obtain ⟨v,vindex,vcheck⟩ := scope.2.2
 have same : v = acc6 := Option.some.inj (vindex.symm.trans index6)
 subst v
 exact (NMX_R7_RelReads241.fold L V verify packet a domain validated acc0 acc6
  proofData checkpointData scope.2.1 index0 index6 read0 read6 vcheck scope.1) env'''
#print axioms fold
end NMX_R7_RelValidate241
