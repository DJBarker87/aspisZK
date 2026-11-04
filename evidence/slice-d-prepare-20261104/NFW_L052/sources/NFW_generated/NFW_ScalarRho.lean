import NFW_Invert
import NFW_PreparedCalls
import NFW_SampledDomains
set_option autoImplicit false
namespace AspisR1.NFW_ScalarRho
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Successful scalar_k returns the actual sampler output for the actual
transcript block, for arbitrary fromQm boundary. No canonicality or
independently selected digest output is assumed. -/
theorem sample {H : Type} (B : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
 (before last : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (rho : aspis_core.field.QM31)
 (run : PreparedModel.scalar_k B D before row payload=ok (rho,last)) :
 ∃ block, transcript.Transcript.block D before row payload=ok (block,last) ∧
  AspisR1PublicPreparation.sampler.qm31_sample block=ok rho := by
 unfold PreparedModel.scalar_k at run
 obtain ⟨pair,blockCall,run⟩ := NFW_Invert.bind _ _ _ run
 rcases pair with ⟨block,after⟩
 obtain ⟨q,sampleCall,run⟩ := NFW_Invert.bind _ _ _ run
 simp only [lift,bind_tc_ok] at run
 obtain ⟨wide,embed,run⟩ := NFW_Invert.bind _ _ _ run
 simp only [trace.value,bind_tc_ok] at run
 have equal := Result.ok.inj run
 have first := congrArg Prod.fst equal
 have second := congrArg Prod.snd equal
 cases first
 cases second
 exact ⟨block,blockCall,sampleCall⟩

theorem prepared {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (out : verifier.Prepared) (scratch old : Array aspis_core.field.WideExact 29#usize)
 (run : PreparedScratchModel.prepare B D sem v hash old=ok (.Ok out,scratch)) :
 NBF_PowerStep.Canonical (NFW_PreparedPort.prepared out).rho := by
 obtain ⟨hp,hc,row,before,afterQueries,last,rows,queries,scalar,state⟩ :=
  NFW_PreparedCalls.calls B D sem v hash out scratch old run
 obtain ⟨block,blockCall,sampleCall⟩ := sample B.sampling D afterQueries last _ _ out.rho scalar
 exact NFW_SampledDomains.rho out block sampleCall
#print axioms sample
#print axioms prepared
end AspisR1.NFW_ScalarRho
