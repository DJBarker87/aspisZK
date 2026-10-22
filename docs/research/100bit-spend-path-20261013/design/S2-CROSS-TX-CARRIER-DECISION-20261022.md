# Cross-transaction carrier binding: obligation, not closure

Scope: S2/S6 caller transport. Production source is unchanged. The adopted
25866ec331cc7ce27dd9956609c11d32fa8fa58a overlay and approved S4
29cbab431742f7e899870595167efa193a379f0a remain authoritative; historical
b2727acd3abf79315d18b754a260f58f4b1c6326 caller files are identical, as checked
in `evidence/s126-current-caller-20261021/caller-source-adoption-overlay-20261022.json`.

The actual stage1 in programs/r1-cost-probe/src/r1_pool_adapter.rs:946 reads
proof/public accounts0/1 and writes checkpoint account2. Stage2 at994 reads
proof account0 and checkpoint account6 and reconstructs public bytes from
validated Pool state. `require_readonly_buffer` checks invocation flags;
it does not establish cross-transaction immutability or a proof-buffer owner.
Do not infer equal bytes merely because both invocations pass this helper.

crates/aspis-r1-cost-probe/src/verifier.rs:329 writes proof/public digests
into checkpoint offsets16:48 and48:80. The checkpoint reader at396 checks
these digests against the current proof/public plus its checksum. These are
hash checks. Their direct conclusion is equality of digest values; byte
identity needs an additional proved argument. No accepted-run counterexample
has been established here, and this note does not claim a protocol defect.

Recommendation: transport on a proved good collision event, preserving the
existing contract and source. Show that the exact source writer and reader
queries are present in the actual experiment history, that saved checkpoint
provenance selects the corresponding writer, and that the good event implies
proof/public byte identities. Then transport the accepted event and oracle
law to the fixed carriers. This is an implementation/probability proof
obligation, not an assumption to add to a record and call discharged.

The lead's fourteen-field S2CallerFacts interface and OraclePortFrozen2Headline
still require the concrete runtime instance. In particular,
StoredCarrierBinding is a separate premise from AcceptedRunJoin. The existing
1161-read budget and collision term cannot be credited automatically: prove
these exact queries and any prior preparation/retained-checkpoint history
are covered, including cached hits and changed preimages. Do not silently add
queries, alter the failure event, or lower the 100-bit per-attempt target.

No source decision is adopted. Enforcing buffer immutability would be a
separate source/protocol candidate requiring equivalence/security/integration
and artifact re-pin assessment; it is not required merely to continue the
recommended good-event proof. Coordinate collision-event composition with
its owner; this session does not modify S3/S9 or the lead's live worktree.
