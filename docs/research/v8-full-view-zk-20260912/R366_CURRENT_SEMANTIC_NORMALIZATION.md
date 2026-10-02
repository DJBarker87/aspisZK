# R366 current semantic normalization result

The focused target `AspisV8R19/R366SemanticNormalization.lean` compiled successfully from the saved source snapshot. Its promoted research source is byte-identical to the successful compiler input (SHA-256 `8c5241c9b09576556d12d5e60d43e224244e865202ce32a80c7dc88a0a22bd2d`). The complete source, logs, receipts, dependency replay, initial cache inventory, and verification checker are in [the R366 evidence bundle](evidence/r366-semantic-normalization/README.md).

R366 proves a universal normalization identity for degree-at-most-27 polynomial walks satisfying each incoming-carry boundary-sum equation. It proves that equal terminal carries imply full 271-coordinate covector compatibility, including the initial carry-difference coordinate, for every field challenge, including 0 and 1. The result is conditional on those generic degree, boundary, walk, and endpoint hypotheses.

The actual source’s degree/interpolation/boundary/endpoint obligations are not discharged here. C1/H1/G coverage, p0/p2/channel coefficients, legal-mask restrictions, posterior bijections, adaptive/shared-oracle and seed laws, commitments, retries/failures/publication, explicit-loss simulation, and soundness remain open. R366 is a formal normalization lemma and does not by itself close a source-semantics or security gate.
