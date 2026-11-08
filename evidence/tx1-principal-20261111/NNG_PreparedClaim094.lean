import NNG_PreparedFacts094
import NNG_SemanticAt094
import NGU_PreparedClaim
import NHS_CanonicalPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedClaim094
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NFN_LPi_FieldValues
/-- The SAME powers producer and the SAME semantic/compact provenance
establish the claim field required by the checkpoint writer. -/
theorem canonical (input : LIBC_PreparedLaw.Args) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (ev : List RSL.Event)
 (semantic : NNG_SemanticAt094.SemanticAt env input.1)
 (domain : LIBC_PreparedDomain.Domain input)
 (returned : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ev⟩) :
 OraclePortCkptAbi4Decode.CanonicalWide
  (CheckpointBytes3Namespaces.toE (NFW_PreparedPort.e p.claim)) := by
 have native := NNG_PreparedFacts094.emitted input env p g ev returned
 have model := (NGN_EmittedEq.source NHL_PreparedScalars.actual (LIBC_PreparedLog.digest env)
  input.1 input.2.1 () input.2.2).symm.trans native
 rw [NHL_QueryDomain.dictionary] at model
 have fields := NNG_PreparedFacts094.canonical input env p g ev returned
 obtain ⟨powers,powersRun,samePowers,_,_⟩ := NFW_PreparedProducer.scratch
  NHL_PreparedScalars.actual.sampling (LIBC_PreparedLog.digest env) input.1 input.2.1 () p g input.2.2 model
 have claimed := (NFW_PreparedCalls.calls _ (LIBC_PreparedLog.digest env)
  input.1 input.2.1 () p g input.2.2 model).2.1
 obtain ⟨B,pub,pre,before,ch,obs,finish⟩ := semantic
 obtain ⟨compact,old,compactSize,oldSize,checked,expanded⟩ := domain.2.1
 obtain ⟨claim,canon,call⟩ := NGU_PreparedClaim.packet B (LIBC_PreparedLog.digest env)
  pub pre before ch obs input.1 finish compact old input.2.1.y1 compactSize oldSize checked expanded
  (NFW_SampledDomains.toNative p.gamma) (NFW_SampledDomains.toNative input.2.1.inactive)
  (NFW_SampledDomains.toNative p.kappa) fields.1 domain.2.2.2.2.2.2 fields.2.1 powers powersRun
 rw [NFW_SampledDomains.roundtrip,NFW_SampledDomains.roundtrip,←samePowers] at call
 change AspisR1ClaimPreparedBridge.claimPublic (LIBC_PreparedLog.digest env) input.1
  input.2.1.y1 input.2.1.inactive g p.kappa=ok (.Ok p.claim) at claimed
 have same : p.claim=NFW_PowersCohort.toPublic claim :=
  core.result.Result.Ok.inj (Result.ok.inj (claimed.symm.trans call))
 rw [same]
 exact NHS_CanonicalPorts.claim claim canon
#print axioms canonical
end AspisR1.NNG_PreparedClaim094
