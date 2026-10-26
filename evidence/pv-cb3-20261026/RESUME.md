# cb3 resumed source-law work

Resume base: 54f2ac877f. Fresh budget: 100 Lean compiles / 15 Kani runs.
Env J IDs: 35600–35899; old IDs blocked and never reused.
Read shared pv-common, restored flag, prior HANDOFF/ROWS/FINAL, root AGENTS
Security and proof discipline, r1p-common, local-lean. New local Mac compiles
are forbidden. Native source frozen; only cfg(kani) instrumentation is allowed.
Published PV_CB3 statements remain unchanged. Endpoint premises removed: 0.

Baseline: this worker 4 ROW-DISCHARGED(candidate), recount2 candidate40→44,
OPEN110→106 excluding sibling changes; V246 needs deduplication.

Priority op51/V195: previous native evidence covers only WideExact::new image.
New proposed harness directly fills all eight private u32 fields in an in-module
cfg(kani) module. It uses the retained extracted flat reference body verbatim,
with `aspis_core::` changed to `crate::` because this module is inside aspis-core.
No input assumptions or canonicalization. Source/ref gate has not passed yet.
The new carrier_complete lemma exposes that these eight fields cover every
extracted carrier. An installed equation alone earns no row credit.

The restored cache lacks cb3 lean-objects despite the launcher note saying they
survived. ProverRwFullTypes/ExternalFuns are available in the shared/union cache;
ProverRwDictionaryBytesSource is missing and requires a charged focused rebuild.
No cache absence is being treated as a stop or proof result.

Admission refused at 22:35:59 UTC: populated bounded reservation51942260736B +
8GiB =60532195328B >59055800320B limit. Zero charged runs. Second read at
22:38:53 remained refused (174s after first; six seconds early; no scope started).
Next admission will wait at least180s after this second refusal.

Op223/V240 early review: sibling extraction failed with Not_found in
collapse_ctx_following_sequence at a borrowed iterator loop. No unchanged
replay is planned. A bounded Kani witness would not prove arbitrary slice
length; retain OPEN until a complete source interpretation is available.

| op | row | resumed status | theorem / next gate | receipt |
|---:|---|---|---|---|
|51|V195|OPEN pending unrestricted native P6|PV_CB3_Op51Arbitrary.op51_source (draft)|arbitrary_bytes.rs; admission logs|
|223|V240|OPEN; current-crate built-MIR extraction prepared|unchanged logup.rs included under cfg(kani)|op223-sibling-check-resume.json|
|253|V260|OPEN; raw index panic branches must be retained|no proposed closure|op253-sibling-check-resume.json|
|258|V264|OPEN; rows beyond mask bounds must fail|no proposed closure|op258-sibling-check-resume.json|

Op223 next extraction changes the MIR context: include the original unedited
logup.rs under cfg(kani) in the current extraction crate, rather than extract
its dependency optimized MIR. This is a source/graph change, not an unchanged
failed Aeneas replay or a shipped implementation modification.
