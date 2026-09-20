# V8 privacy: decision and necessary repair boundary

2026-09-20; evidence base `a100b7c8`. Research only; no production change.

## Plain-language verdict

V8 is not established private. There is a demonstrated secret-dependent
disclosure in controlled, complete, accepted same-public proofs. Its
probability under the intended real experiment is not established. Therefore
neither a practical-attack claim nor a safe-private-release claim is justified.
This does not establish that the entire design is irreparable.

## What the existing certificate rules out

Let O be the eight column-zero C1 opening values at fibres 4 and 6. The
retained scalar vector λ annihilates the existing column-zero mask image,
but evaluates to the nonzero value 490597912 on the demonstrated same-public
witness difference. Consequently λ·O cannot be made witness-independent on
this fixed observation by selecting another value of the existing mask.
This is the meaning of the retained raw certificate, not a new assumption.

The complete controlled host proofs show that this statistic survives the
rest of the construction. `RawScheduleExtension.lean` proves that including
other queried fibres does not erase it. The literal serializer exposes these
values; hiding their earlier commitments cannot hide their later plaintext.

Therefore the following are **not repairs of this fixed-observation leak**:

- changing the seed distribution while retaining the same C1 mask image;
- adding only H1/G freedom, without changing the exposed C1 values;
- proving more early semantic-message surjectivity;
- stronger commitment hiding with the same plaintext openings.

Those changes can affect the query distribution. That is different from
removing the raw separator: they would need a separate proof that unsafe
publication becomes sufficiently unlikely. No such proof is currently held.

## Necessary alternatives, not sufficient designs

1. **Change the exposed C1 observation or its masking.** For every relevant
   same-public witness difference, the legal mask image must cover the
   resulting observable difference, jointly with prior observations. For the
   known certificate, retaining exactly the same exposed statistic requires
   eliminating its nonzero witness offset or adding a legal C1 mask direction
   on which λ is nonzero. Fixing this one direction alone is not full privacy.
   Any new direction must preserve relation correctness, binding/soundness,
   chronology, proof-size and compute constraints.
2. **Prevent unsafe full views from being published.** A complete safety gate
   could be investigated, but a blacklist of {4,6} is not a coverage proof.
   The gate must address the whole conditioned view, have justified release
   probability, and account for visible failures, retries and stopping.
   Filtering itself can reveal information. No usable gate is proved here.

An equivalent redesign could stop exposing these raw values altogether,
but that changes the proof protocol and needs a new correctness/security
analysis. None of these alternatives is implemented or authorized by this
research task. In particular, earlier suggestions to add helper-only masks
address a different H1 obligation; they do not fix this C1 certificate.

## What decides the present protocol's attack verdict

### The existing research gate is not deployed protection

Source inspection at `328c7a58` confirms that
`crates/aspis-prover/src/v8_privacy_publication.rs::review_for_publication`
returns an error for both raw-precheck outcomes. Its only call sites in the
crates tree are its own unit tests; `lib.rs` merely exports the module.
The recovered `performance-host/Cargo.toml` depends on `aspis-core` and
`aspis-statement`, not `aspis-prover`, and the authenticated performance
source writes proof bytes directly after verification/corruption controls.
Those controls test proof validity, not full-view privacy.

Thus the research gate neither proves a useful release probability nor
protects the recovered host's output. Integrating its present fail-closed
behavior would stop publication, not repair privacy while retaining service.
No such production integration was performed. This is read-only source
evidence; unchanged gate unit tests were not rerun.

### Quantitative attack question

The remaining quantitative question is the unconditioned probability of
publishing the revealing observation in the intended source-bound experiment.
The ideal uniform-query pair probability `11/1636171776` is **not** an actual
Aspis advantage bound until oracle freshness, reach, failures and publication
are connected to that experiment. The current fixed-seed host is not that
entropy-backed interface. Local field and circle lemmas close parts of this
analysis, not the final verdict.

Keep the negative regression and this repair constraint regardless of which
route is chosen. Do not label V8 private or a candidate repair complete on
the strength of finite examples or conditional compiler lemmas.
