# Excluded drafts and repairs

- L001: direct reduction of the opaque iterator and endpoint operations does not establish their equations. Replaced by NFA_Iterator.next and NFE_NFA_BatchDomain.endpoint laws.
- L002–005: finite specialization/rewrite elaboration and UScalar literal proof transparency. Named next0–next6 specializations avoid the tactic-instance mismatch; L006 passes. No large numeral/recurrence normalization is used.
- L007: `<iter` lexes as the `<i` notation followed by `ter`; added spaces. L008 passes.
- L009: a successful simp already closed body, so the trailing rfl reported no goals. Removed that redundant tactic; L010 passes.
- L013: omega on the large fixed fold coefficient reached default recursion depth. Replaced by symbolic bound transitivity and monotonicity, h.trans cap. L014 passes; no recursion/heartbeat limit was raised.
- L016: manually repeated dependent cut syntax failed to elaborate. Unfolded the existing named window definition instead; L017 passes.

All failed attempts and their complete diagnostics/#print lines remain archived, and are excluded from credit. Shared launchers, admission, shims, caches and host infrastructure were not edited. Own scripts are prefix adaptations or proof/evidence validation only. The setup log's duplicate12MB manifest line was replaced with a hash reference to the single NFM_CACHE_IMPORTS.json copy; all imported hashes are retained there.
