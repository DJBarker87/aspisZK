# Canonical route obligations

1. Snapshot decoding: exact EJR-resolved `AspisR1TerminalDecoder.Funs`.
   Source authority, blob and hash are in focused-resolution.json. The matching
   current Rust decoder first checks length/magic/version/reserved/format;
   then decodes current-root and all20 frontier digests canonically; constructs
   one snapshot; validates nonzero bindings, sequence=index, capacity, and
   canonical words; returns that very snapshot. DecoderReturn29 targets this
   last association. DigestLoop29 targets exact loop success iff canonicality.
2. Public validators: CommonDomain29/Errors29, WithdrawalDomain29/Errors29,
   TransferDomain29/Errors29 enumerate all first-error paths of the pinned
   extracted validators. Generated definitions retain primitive return values
   rather than assuming totality. These are not outer-wrapper equivalences.
3. Outer wrappers: frozen source lane_root; temporary public/context anchor;
   public validation; runtime pool/domain/sequence/asset; spent set; input key,
   salt, membership canonicality; positive input below2^30; index below2^20;
   pair validity/spendability; snapshot pool/domain; variant conservation;
   then actual inner compiler. Outer extraction is the next source-association
   task; no hand-written success callback is substituted for it.
4. Actual inner compiler success/error characterizations are inherited from
   CompilerDomainProof28/RejectionProof28, with arbitrary primitive dictionaries.
5. Returned payload packaging/cached compiler law is inherited from
   PreparedPayload28. Neither packaging nor decoder alone proves Admission.
   Prove Checked and semantic Admission before claiming HonestInput.
6. Exact owner coverage follows only after1–5. V038/V045 remain subsequent.

Conservation29 is checked at38183; its predicates are arithmetic guard facts,
not a declaration that positive change is the complete canonical route domain.
The raw-output probe is a retained failed candidate, not a stop or a finding.
