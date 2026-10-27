import F3L_SourceNumeric
import Port3_FlushInstall
set_option autoImplicit false
namespace AspisR1.F3L_RhoCanonical
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem sample (block : Array U8 32#usize) (rho : aspis_core.field.QM31)
    (sampled : sampler.qm31_sample block=ok rho) :
    Port3_FlushInstall.Canonical (Tx1Q_Carriers.k (currentQ rho)) := by
  obtain ⟨q,success,canonical,_⟩ := SamplerTransport.sample_total block
  have same : q=rho := Result.ok.inj (success.symm.trans sampled)
  subst q
  exact canonical

theorem scalar {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (payload : Slice U8) (rho : aspis_core.field.QM31)
    (success : PreparedModel.scalar_k B D before 32#u8 payload=ok (rho,after)) :
    Port3_FlushInstall.Canonical (Tx1Q_Carriers.k (currentQ rho)) := by
  obtain ⟨block,_,sampled⟩ := PAln_OpeningCalls.rho_success B D before after 32#u8 payload rho success
  exact sample block rho sampled

#print axioms sample
#print axioms scalar
end AspisR1.F3L_RhoCanonical
