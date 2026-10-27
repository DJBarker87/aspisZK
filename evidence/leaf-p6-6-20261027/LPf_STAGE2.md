# Arithmetic continuation

LPf_L005 passes LPf_CoreReduction.same/source: both actual extracted reducers
are equal despite the placement of the u32 cast; total exact residue for all U64.
LPf_L008 passes LPf_BaseMultiply.source: for every two U32 (no canonical input
restriction), actual extracted M31.mul succeeds and returns their natural product
modulo P, canonically. Exact natural product/no-overflow is proved separately.
L006/L007 failed constant-unfolding goals; their sorryAx recovery output is
excluded. All accepted new theorem audits are standard-only.
These are source-model results under the existing extraction boundary. They are
not evidence that either timed-out Kani exact multiplication contract passed.

K011: private reduce contract PASS, all u64/no precondition. K012: four raw
coordinates TIMEOUT. K013: isolated raw coordinate2 TIMEOUT; neither installed
as verified. K014: QM31 byte-writer contract TIMEOUT; split at actual CM31 writer.
The remaining raw-product gate needs limb-product decomposition; caller checks
must not use its unproved specification. K008–010 compilation failures retain
missing frozen source includes and the corrected Kani old(x) syntax.

Full resolved graph equality is additionally checked against the retained frozen
LPe graph (see LPf_GRAPH_AUDIT.md). No lock drift, shipped edit, cap raise, swap,
new trust item, actual-top premise removal or full release result is claimed.
