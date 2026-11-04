# NFC findings

The ax2 fixture gate passes; no auditor finding.

L006/L007 are failed local elaborations (unknown scalar API / closed checked-add proof); L008 fixes the proof and passes. No failed attempt is credited.

L009 imported historical LPf_PublicDotAllStates and failed the coherent headline import: `S1ExtractedRoundChildrenV1` collides with `RPz7_S1ExtractedRoundChildrenV1`. L010 replaced the finalizer with NEI's already narrowed modules but still imported legacy LPf_ArrayFour, which itself imports LPf_ReductionWord. Neither attempt is credited. Replace that generic carrier lemma with a new NFC module with only headline imports; no historical module or shared object is edited.

L016: the NEV_StageWideFields imported field forest has a legacy-owner collision against the headline-selected carrier. Excluded. NFC_ScalarAdd / NFC_AddDomain replace only the needed add-domain laws with direct proofs on the selected definitions (L022/L023).

L026: full read/push source normalization reached the fixed 200000 heartbeat threshold. It was not rerun unchanged. Sources were split into first/later continuation joins (L028/L029), then composed in L033; no limit was raised.

L040: the legacy NEV_EbyDomains forest has the same owner collision. NFC_RawAssociation (L042), NFC_RawValues (L043), and the private push chain are narrowed from immutable committed proof sources, with NFC namespaces. Source provenance and import changes are recorded in NFC_NARROW_PROVENANCE.json; legacy objects are excluded.
