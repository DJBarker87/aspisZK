import RawActualAnnotatedPolynomialRun
import RawGenericPolynomialSumcheckChainMap

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualAnnotatedPolynomialWideChain

open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain
open AspisR1PublicPreparation.RawGenericPolynomialSumcheckChainMap
open Aeneas Aeneas.Std Result

abbrev E := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev W := AspisWideTower.WideExact

/-- The actual ten-round annotated chain remains the same ordered sequence of
polynomial/challenge entries after mapping its QM31 values into WideExact. -/
theorem annotatedRun_to_wide_chain {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (events : List (Usize × U8)) (initial final : Outcome H)
    (entries : List (RoundEvidence D pre))
    (hrun : AnnotatedRun D pre events initial final entries) :
    Chain
      (algebraMap E W (DecodeMain initial.1))
      (algebraMap E W (DecodeMain final.1))
      (entries.map fun entry =>
        ((polynomialOf entry.coefficients).map (algebraMap E W),
          algebraMap E W (challengeOf entry.q))) := by
  have hchain := annotatedRun_to_chain D pre events initial final entries hrun
  have hmapped := Chain.map (algebraMap E W) hchain
  simpa [List.map_map, Function.comp_def, pairOf, polynomialOf, challengeOf]
    using hmapped

#print axioms annotatedRun_to_wide_chain

end AspisR1PublicPreparation.RawActualAnnotatedPolynomialWideChain
end
