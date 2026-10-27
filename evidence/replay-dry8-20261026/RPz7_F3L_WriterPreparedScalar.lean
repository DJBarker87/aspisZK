import RPz7_F3L_WriterSourceScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterPreparedScalar
open AspisR1PublicPreparation
open F3K_CheckpointPreparedFields
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec

theorem fields (out : verifier.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22 := (writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out) a size qb)) :
    let pm := CheckpointBytesBlocks.prepared (CheckpointBytesBody.fields (writerPrepared out) a size qb) canonical
    pm.gamma=AspisR1CurrentPreparedClaim.Concrete.decode (AspisR1ClaimPreparedBridge.toClaimE out.gamma) ∧
    pm.kappa=AspisR1CurrentPreparedClaim.Concrete.decode (AspisR1ClaimPreparedBridge.toClaimE out.kappa) ∧
    pm.rho=F3L_RhoMeaning.decode out.rho ∧
    pm.state=AspisV8R19.SqueezeOracleBridge.decodeState out.state := by
  refine ⟨?_,?_,?_,rfl⟩
  · exact F3L_WriterSourceScalar.exact_e out.gamma canonical.gamma
  · exact F3L_WriterSourceScalar.exact_e out.kappa canonical.kappa
  · exact F3L_WriterSourceScalar.exact_k out.rho canonical.rho

#print axioms fields
end AspisR1.F3L_WriterPreparedScalar
end
