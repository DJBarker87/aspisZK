# Stage 2: actual small source helpers and SDK/seed leaves

Kani allowance25/25 is now exhausted;15 pass,9 timeouts,1 compile failure.
No further Kani will run. Lean composition CONTINUES: the Kani budget is not
a stopping condition. No native accepted P1 certificate or global row removal.

Native additions: fixed-construction original unique guard derives actual0!=9
(K011); exact count/error guard (K018); original AS8C codec length0..9 (K008);
complete original payer/System result/error predicate with SDK IDs (K020); all
remaining master identity/policy scalar/byte-array fields bound to SAME arbitrary
384 image (K007/010/013–017, complementary to PoolT header/chronology gates);
real shared read -> strict decoder -> Box bump snapshot (K022), all-result
selected-byte frame and mutable reborrow after guard drop (K023); exact four
signing-seed contents from strict decode of SAME arbitrary192 image (K024).
Metadata/PDA and whole-master-wrapper acceptance are excluded from the Box cut.

Native full unique/P6 equivalence (K012) and original planner same decoded
master output/selected repeat-lane gates (K021/K025) still time out. K025's
2112KiB time report misses descendants; raw cgroup peak is separate. No source
fixture restriction was promoted to arbitrary accepted P1 coverage. K019's
wrong native_loader import compile failure is corrected by K020 matching the
original processor's pinned solana_sdk_ids import. No caps raised or unchanged
timed-out harness replayed; failed artifacts remain excluded.

Aeneas005 extracts actual original count/payer/System/instruction helpers.
Canonical owned metadata, concrete SDK IDs, repr(u32) error conversion and pure
std key/slice equality are documented adaptations, not a whole caller bridge.
PoolS2_Count, Payer/PayerExact and Instruction prove exact acceptance/guard and
error properties from those SAME helper invocations. No independent metadata
admission or instruction-validity premise remains in their local acceptance laws.

Aeneas006 extracts six actual pure PDA seed/matcher helpers. PoolS2_PdaSource
keeps only REAL SDK create/find operations as explicit value functions; no
caller-success, output or lifecycle contract is a field. Query/effect/runtime
interpretation stays OPEN. No external template axiom is imported. Symbolic
PDA/decoder/caller composition continues under the remaining Lean budget.

Proof-only host crates may resolve transitive build/proc-macro dependencies
differently from the production workspace lock. Their exact resolved locks
and SDK leaf pins will be collected; these are scoped native host checks, not
a coherent frozen ELF rebuild, release adoption or source-to-SBF refinement.
No shipped/cfg(kani) source, feature, lock, key, account or fund changed.
Default/devnet/Pool inherited ELF pins remain unchanged; no rebuild trigger.
