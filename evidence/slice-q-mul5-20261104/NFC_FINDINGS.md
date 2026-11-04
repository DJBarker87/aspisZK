# NFC findings

The ax2 fixture gate passes; no auditor finding.

L006/L007 are failed local elaborations (unknown scalar API / closed checked-add proof); L008 fixes the proof and passes. No failed attempt is credited.

L009 imported historical LPf_PublicDotAllStates and failed the coherent headline import: `S1ExtractedRoundChildrenV1` collides with `RPz7_S1ExtractedRoundChildrenV1`. L010 replaced the finalizer with NEI's already narrowed modules but still imported legacy LPf_ArrayFour, which itself imports LPf_ReductionWord. Neither attempt is credited. Replace that generic carrier lemma with a new NFC module with only headline imports; no historical module or shared object is edited.
