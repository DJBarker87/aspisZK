# Historical component pins versus later build source, 2026-10-25

Correction: 25866ec331cc7ce27dd9956609c11d32fa8fa58a is the historical
component snapshot used by our native experiments, not a new whole-release
freeze. The newly merged authoritative release ledger (research merge58b172d801)
records default/devnet compiler source4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
and keeps all source/artifact/security closure gates open. Do not promote our
historical component checks to that later implementation without a scoped
source/dependency/caller association. The user target remains <=2^-100 per
attempt without grinding credit; no campaign/security metric change is made here.

Read-only immutable Git comparison, no compiler or cache access:

- Entire verifier.rs, r1_semantic.rs, r1_wire.rs, transcript.rs, transport.rs,
  trace.rs and sampler.rs are byte-identical between the two commits.
- Core field.rs and field/wide_exact.rs are identical. Of88 pinned core source
  files, only state_only_prefix.rs differs: the two-coordinate [7,6] loop was
  written as two assignments. No whole transitive-context identity is inferred.
- Exact complete Prepared impl, prepared_claim, powers, field, EbyKDot struct,
  EbyKDot impl, observer and first_decoded items are identical.
- Entire weights.rs and fast_pairing.rs differ. Fast-pairing changes include
  typed shift RHSs, explicit4-coordinate maps/loops and checked_q match syntax.
  Those lower bodies require their own source re-pin/equivalence; same public
  function names do not justify attributing old math/source evidence to them.
- Program lib.rs adds a test module; actual adapter production routing changes
  from inline borrowed stage1/stage2 to r1_pool_adapter_owned.rs. This is a real
  caller-source difference, not an observer/codec theorem closing actual SDK
  binding. S2/current native interpretation remains separately owned/open.

The unchanged selected source is useful evidence for a narrow re-pin, not a
completed re-pin. In particular the native field32 check retains its old full
core import hashes until the changed core context is associated explicitly.
Historical normal-callee constructor/claim checks do not verify the changed
lower arithmetic implementations or later SDK dispatch merely because their
selected outer bodies are identical. Source dictionaries and native caller
instances in our SDK theorems remain explicit hypotheses.

No production source was edited, no candidate was adopted, no ELF reproduced,
no historical successful proof recompiled and no source change on another
session's track was made. source-only focused-extractor-proof-packet-v1 data:
evidence/s126-current-caller-20261021/freeze-reconcile-20261025/comparison.json
and changed-files.diff. The checker validates13 whole files,8 exact selected
items and88 core source hashes directly from both immutable Git objects.

Required next association: use the later actual owned-adapter source (S2 owner),
re-pin changed lower arithmetic/source contexts with their owners, and connect
all exact same-execution source/native/oracle facts to the coherent caller and
release artifacts. Source-only comparison is not compiler replay, theorem
transport, accepted axioms audit or satisfaction of those source premises.
Both actual implementation-linked targets remain not established.
