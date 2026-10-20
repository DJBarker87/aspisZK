import R4TransportGammaRank
import R1SourceSamplerByteRank

/-! The optimized gamma integer reference equals the retained byte/digit
model. Refinement of the mutable Rust helper loops remains separate. -/
set_option autoImplicit false
namespace AspisR1.R4TransportWideReference
open Aeneas Aeneas.Std

theorem block_quotient_bound (block : Array U8 32#usize) :
    SourceSamplerByteRank.rank block / R4TransportGammaRank.p8 < 257 :=
  R4TransportGammaRank.quotient_bound _ (SourceSamplerByteRank.rank_lt block)

theorem gamma_reference_eq_byte_model (block : Array U8 32#usize) :
    R4TransportGammaFold.folded (SourceSamplerByteRank.rank block) R4TransportGammaRank.p8 =
      SamplerAddDigits.digitsValue SamplerMachineBounds.P
        (SourceSamplerByteRank.gammaBytes block) := by
  rw [R4TransportGammaRank.gamma_rank _ (SourceSamplerByteRank.rank_lt block),
    SourceSamplerByteRank.gammaBytes_value]
  rfl

#print axioms block_quotient_bound
#print axioms gamma_reference_eq_byte_model
end AspisR1.R4TransportWideReference
