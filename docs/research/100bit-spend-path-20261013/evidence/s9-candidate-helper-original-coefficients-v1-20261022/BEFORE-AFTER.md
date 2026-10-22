# Premise removal and retained contract

Before: `AspisR1S9CandidateTopHelperMapV1.candidate_top_success_maps_to_p6` takes actual htop, hextra, hap1 and `CandidateSuffixTransport ap1`. The latter universally assumes that the same successful candidateAfterTerms call maps to the P6 continuation at its mapped flow.

After: `AspisR1S9CandidateTopTransportDischargerV1.candidate_top_success_maps_to_p6` has the same top-call correspondence conclusion and htop/hextra/hap1 conditions. It constructs that suffix transport via `candidate_after_terms_success_maps`, using the same source call, same PERM read, same term values, and a proved equality of the two fieldwise flow maps. No output, read witness or trace is replaced. This is genuine discharge of that transport premise.

The separate coefficient theorem adds explicit hp0 canonicality to obtain the stronger original-coefficient conclusion. It is not a claim that the weaker top-map theorem alone entails coefficient semantics. Its remaining premises are only actual top success plus the three stated input canonicality contracts; the full source is retained in this packet.

Neither theorem proves those input contracts from the frozen caller/parser, candidate adoption, all-input helper totality, artifact equality or the complete security experiment. Canonicality of the successful returned cells is proved separately, under the same input contract.
