import NDO_JHl_Kappa06
import NDO_JHk_PreparedScalarBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_ClaimKappa
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

def value : Nat → AspisWideTower.WideExact
  | 0 => 1
  | 1 => CheckpointBytes5Output.ofE JFq_Kappa.scalar
  | 2 => JHl_Kappa02.value
  | 3 => JHl_Kappa03.value
  | 4 => JHl_Kappa04.value
  | 5 => JHl_Kappa05.value
  | _ => JHl_Kappa06.value

theorem numeric (n : Fin 7) : CheckpointBytes5Output.ofE JFq_Kappa.scalar^n.val=value n.val := by
  fin_cases n
  · rfl
  · exact pow_one _
  · exact JHl_Kappa02.source
  · exact JHl_Kappa03.source
  · exact JHl_Kappa04.source
  · exact JHl_Kappa05.source
  · exact JHl_Kappa06.source
#print axioms numeric

/-- Exact seven kappa weights on this preparation's actual return. The six
claim dots and their weighted sum remain separate obligations. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) (n : Fin 7) :
    CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.kappa)^n.val=value n.val := by
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  rw [fields.2.1]
  exact numeric n
#print axioms source
end AspisR1.JHl_ClaimKappa
end
