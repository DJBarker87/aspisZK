# Semantic payload opening-view bridge

Focused target `R1SemanticPayloadOpeningView` packages the checked 25-row typed payload view with the existing `R0P.MaskView.openingViewZ_of_parsed` theorem. The explicit C2 base and circle distinctness/non-rationality premises are preserved. It is a model-view lemma; it does not connect unified raw messages or source bytes to these payloads, nor does it prove opening acceptance or the J1 spend relation.

Attempt a is preserved as a failed index-bound proof. Attempt b is green (2.24s, 3,568,240 KiB peak RSS, zero swap, 4G/6G/swap0). The green `#print axioms` output is standard only: `propext`, `Classical.choice`, and `Quot.sound`. The present-cache supplement is adjacent at `../semantic-payload-view-present-cache-20261015.json`; it distinguishes current source/cache observations from historical source provenance.
