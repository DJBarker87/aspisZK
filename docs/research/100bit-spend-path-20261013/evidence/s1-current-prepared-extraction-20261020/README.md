# Current Prepared gamma-scratch re-pin (S1), 20 October 2026

**PROVED, conditional child boundaries. S1 overall remains OPEN.**

Source baseline `f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5`. Twenty current production declarations are copied exactly into the extraction input. The selected production method is `verifier::Prepared::new`, now taking caller-owned `[WideExact;29]` gamma scratch. The second selected declaration is the extraction-only `prepared_entry` wrapper, which forwards this scratch; it is not a production entrypoint. `prepared_claim` is an explicit opaque child during extraction, not a newly proved implementation.

Charon and Aeneas both pass. The LLBC is pinned by SHA only (`c7f3a1ca8f3f8e57f3e715a1f56721b08cfa6d38bd19044918ad6ae360cb7a16`). The complete current Prepared body is emitted. Generated external templates are untrusted diagnostics: none is imported by the checked model. The retained canonical carrier union is byte-identical to the accepted Types/Funs owner; it is reused without an unchanged replay. The binder changes only listed identifiers and adds the explicit operation bundle, with raw/bound body hashes recorded.

Five new focused modules compile, with six standard-only axiom reports:

- `CurrentPreparedScratchModel`: source-shaped preparation and entry, explicitly parameterized by sampling, powers, and cached claim.
- `CurrentPreparedScratchReachability`: successful new-body execution supplies the ordered sampler/query state trace, the successful powers call, the same returned scratch array, and the cached claim on that exact array. No independent powers/claim success premise is assumed.
- `CurrentPreparedLegacyTransport`: under the named `ClaimsAgree` arithmetic/source correspondence, successful new preparation yields successful retained preparation with the same output. This makes the existing sampler/caller results reusable instead of reproving them against the new scratch API.
- `CurrentPreparedCallerReuse`: removes the independent `ClaimsAgree` premise for sampler/caller reuse by choosing the retained model's arbitrary claim boundary as the current powers-then-cached-claim composition. Every sampler field is preserved. Successful current preparation supplies successful retained caller-model execution directly, with the same output. This does not assert equality to an old Rust claim implementation.
- `CurrentPreparedLiteralTotality`: independently proves all three checked integer additions in current preparation are total: 32+224=256, 30+1=31, 31+1=32. It does not assume overall checked success. Allocation, folded-root unwrap, and child operation totality remain separate.

## Remaining obligations

Actual cached `prepared_claim`/powers semantics and current `tx1`/adapter/runtime bindings still need to be established for the complete soundness relation. The sampler/caller reuse theorem now needs no independent `ClaimsAgree` hypothesis: it interprets the generic retained claim boundary with those same current operations. Complete adopted-format source correspondence is not established by this packet. Historical base52 source carriers and each child API still need their current source correspondence, despite the exact common generated declarations. This packet is not whole-Prepared totality, a whole-transaction proof, an artifact pin, or the 100-bit theorem. No production source changes.

The upcoming stage-2 borrow fix reopens any changed Prepared/body/carrier dependencies; a changed parent file hash alone does not alter an unchanged selected method. Fresh source identity must be checked at the final combined freeze. S8 stage 2 waits for the assigned incoming generated Lean.

## Reproduction and diagnostics

`prepare-current.py --revision <ref> --out <kit>` preserves exact production cuts. Its synthetic entry adds the new scratch argument. The retained generic scanner had included the preceding Error enum's inline cfg variants in the Phase cut: the corrected exact Phase span is pinned. The unselected `verify_observed` body is omitted because its new split helpers are outside this selected cone; it is not replaced by invented semantics. The first two Charon attempts failed before emission on these extraction-layout issues, not verifier source errors. The v3 admission initially failed without launching; v3b succeeded after host capacity changed. Producing runner scope prose is historical; `root_target=prepared`, commands, inputs, and receipts delimit the actual scope.

`verify-current-cuts.py <kit>` checks all twenty exact Git spans, fragment/kit hashes and scratch API. `bind-current.py --generated <raw-dir> --out <dir>` reproduces the checked bound model. Focused runner configurations record exact imports, toolchains, source revision, caps and target. Lean failures v1–v7 are diagnostic-only variants of the transport proof; the selected v8 proof is green. No unchanged package/manifest replay, binaries, or new global axioms are included.
