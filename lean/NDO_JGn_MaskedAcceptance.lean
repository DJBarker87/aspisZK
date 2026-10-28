import NDO_JGn_TerminalIdentified
set_option autoImplicit false
namespace AspisR1.JGn_MaskedAcceptance
open Aeneas Aeneas.Std Result

theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H) :
    ∃ terminal mask,
      FIq_Terminal.terminal JFs_PublicSerialization.value JFu_ClaimsData.claims
        JFm_PartialAlpha.a10 JFm_Begin.challenges=ok (.Ok terminal) ∧
      FIp_SemanticArithmetic.mask JFu_MaskInputs.c1 JFu_MaskInputs.maskOnly
        JFu_MaskInputs.g JFu_MaskInputs.point=ok mask ∧
      JGb_MaskedArithmetic.run terminal mask=ok JGd_NumericData.running :=
  ⟨JGd_NumericData.neededTerminal,JGd_NumericData.mask,JGn_TerminalIdentified.source D hash,
    JGd_MaskSource.source,JGd_MaskedGate.source⟩
#print axioms source

theorem formula : FIp_SemanticValues.decode JGd_NumericData.mask +
    FIp_SemanticValues.decode JFm_Begin.challenges.eta *
      FIp_SemanticValues.decode JGd_NumericData.neededTerminal +
        FIp_SemanticValues.decode JFu_ClaimsData.q115 =
          FIp_SemanticValues.decode JGd_NumericData.running := JGd_MaskedGate.formula
#print axioms formula
end AspisR1.JGn_MaskedAcceptance
