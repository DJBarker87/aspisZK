# LIBB TX2 library handoff

Target not yet established. Branch codex/cx-libb-20261107; base 198f29a487ce5a72061c3ff09063c8cf176e7f11. No row credit is claimed; the ledger gate decides. Scope is LIB0 modules6–13, RSL revision3. The only scope budget is300 serial Lean/link/audit scopes,0 Kani,0 extraction.

## Established claim

Modules6–11 instantiate one concrete `LIBB_PoolLib.library : RSL.PoolLib`, with all20 fields and no Prop/Ops/child-success/allocator-success parameter. `LIBB_PoolLib.deployed` fixes the existing deployed IDs. `LIBB_PoolLib.values` instantiates every NND_PoolValues evaluator. `LIBB_PoolLib.scanner_extent` and `LIBB_PoolNoWrite.laws` supply the scanner and no-write facts needed by consumers. Definitions are the deterministic CLOSED source-model graphs at SAME arguments, with the modeled allocation/event arms; native Cut/Windows associations are separate lemmas.

- Module6: merged carriers imported unchanged (L001).
- Module7: policy and four registry/entry values, exact root associations and Returns (through L012).
- Module8: reuse NMX decoder library, exact byte/word/record transport, master/checkpoint graphs and Returns (through L021).
- Module9: request/binding reads, all-eight-word nullifier, CLOSED outputLane (L023/L025).
- Module10: scan/reconstruct allocation graphs, encoder array-by-value (no invented Box), exact return-data emit event, Returns and scanner extent (through L038).
- Module11: complete PoolLib/Values (L039) and concrete no-write laws (L088).
- V2 carrier fields VErr/debug/Root0 are fixed (L041). Module12 tx2auth and module13 full V2Lib are WAITING. No partial bundle is counted as complete.

See LIBB_STATUS.json for each field's defining term, supplying ledger root, bridge and status; LIBB_MODULES.json records module status. This is library instantiation evidence, not proof that a principal candidate or the headline has CLOSED.

## Canonical TX2 support and exact remaining boundary

LIBB_PartitionEnv / Tx2EnvCode / Tx2EnvTrace preserve the original Env.sha256 part lists. C04 partitions are recovered for node and arbitrary truncated leaf views; no partition-invariance property of an arbitrary Env.sha256 is assumed. Earlier flat-H resolved-only support is retained and explicitly uncredited for canonical installation.

L101–L104 normalize both the outer pair and nested dense-point reservation; arithmetic loops remain opaque. L106–L109 derive tag-bound per-occurrence/resolved/stopped parent transport. They bind only REACHED reservation sites and retain the actual finish ABI locations. L114 EnvCommon gives SAME Result/outer chronology or exact stopped prefix/pending query. L116 transports the original four NMN clauses without adding a parser/child-success or global Root0 premise. L117 gives exact ordered rich-record decomposition; L118 exact node/leaf Env replies/events; L119 resolved-only Functional/Returns; L120 complete parser split.

The full canonical graph-of-model observation law must still compose those results with every independently stopped prefix and the actual host EnvRep/f064 association. Only then install the canonical tx2auth field, discharge its full Dom064 gate, build module13 and register the unchanged NNC_ObservedLaw.w weak law for that SAME V0. No native witness choice, native execution image, empty renderer, arbitrary Ops or added success premise is licensed. These remaining obligations are Lean/model/runtime-representation work, not blocked by Kani exhaustion. No historical determinism-obstruction investigation is reopened.

## Hypotheses and validation

No assumptions or trust rows are added or changed. Original supplier own-input clauses remain verbatim. CLOSED child/detail laws in generic bridge lemmas are intermediate premises supplied by the original roots, never newly installed caller clauses. Runtime reservation/hashv observation binding remains a concrete representation obligation. LIBB_CLOSED.json classifies every hypothesis category; LIBB_CALLER_CLAUSES.json retains the original TX2 clauses. Failed elaborations, replacements and retired shapes remain in immutable receipts and LIBB_FINDINGS.md.

L121 passes the focused combined import of ledger25 NMQ_COMBINED_IMPORT plus all delivered LIBB modules; L122 checks every new theorem's actual interface. These cached focused checks are not a cold release replay or source-to-ELF claim. Per-scope exact target/command, exit, wall time, peak RSS, swap, source revision/hash, #print axioms, selected dependencies and Aeneas pins are retained. LIBB_VALIDATION.json and one-line LIBB_TRANSCRIPT.tsv are the final accounting; raw ax2/#print coverage is LIBB_AUDIT_COVERAGE.json. Only successful current-source receipts count. No unchanged timed-out/memory-killed job was rerun; no caps or timeout were raised.

Each scope has fresh running-codex-scope count<6, free disk≥40GB and admission exit0 AND allowed:true; limits6G/8G/swap0/tasks64, Lean-M7000. Waits are not launches. One owned scope at a time; no flock or shared infrastructure modification. Original launchers/reservation/shim and all sibling/session-A worktrees are unchanged. Owned runner repairs and exact imported hashes are retained.

Inherited extraction/tool provenance and source-to-ELF obligations from ledger25 remain; this job performs no extraction and changes no release claim. Headline stays AspisR1.RPx_Deployed.deployed, frozen3, statement-parameter L154, narrowed D188,100-bit PER-ATTEMPT, privacy and the two-transaction design.

## Consumer pickup and retention

Copy committed LIBB sources from this branch with provenance, never modify this or a sibling's live worktree. Pool consumers import LIBB_PoolLib and optionally LIBB_PoolNoWrite; they use the SAME library/deployed/value terms. Full source and compiled-object inventories are retained in LIBB_EXPORT.json / LIBB_EXPORT_PATHS.json under /home/dombarker/project-offloads/codex-cx-libb-20261111/LIBB_exports_20261111, with byte-identical hashes. Merged LIB0–5, NMX reuse and ledger25 objects are reused, not re-proved. All owned caches/TMPDIR are retained; no deletions.

No shipped-source change or ELF rebuild trigger. Inherited pins: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. Frozen crates/r1/Cargo.lock4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275465600469312d1f058cdc91ea2a11f3dc. Artifact pins are inherited, not newly rebuilt/reverified here. No wallet/key/account/fund/authority action, no push. Files>20MB are forbidden; raw walks are losslessly .xz with uncompressed SHA256.

## Final disposition

All300/300 scopes used:70 successful focused Lean targets,1 optimized link,208 distinct own-root raw ax2 audits,21 repaired/excluded elaboration failures. No timeouts or memory kills. Outer scope wall6318.350s; maximum RSS6837528KiB; swaps0. All208 raw walks and every accepted #print axioms report only propext/Classical.choice/Quot.sound. All198 theorem/lemma declarations have an explicit #print axioms. L121 combined import and L122 actual-type inventory pass. Integrity verified717 source snapshots,208 compressed raw SHA pairs,239 stable selected Aeneas object paths,70 retained own objects, every admission/disk/share/cap receipt, no oversized file and no shipped/foreign change. Final retained host free106894204928bytes.

Budget exhausted; no further scope is authorized in this job. Every PoolLib field and VErr/debug/Root0 is DONE in the field inventory, subject to consumer/ledger review. Module12 remains WAITING for the complete canonical full observation law/host association described above; module13 waits precisely on that field. No remaining independent field was withheld behind it. These are Lean/model/representation obligations, not a Kani-exhaustion finding. Target not yet established. No push.

## Resume 2026-11-07

New authorization:200 serial Lean/link/audit scopes (L301–L500),0 Kani,0 extraction. Only modules12 and13. Complete canonical source/native observation fold, retained independent C04 prefixes, rev3 reservation gate and unchanged NNC weak law registration; I.f064 remains integration-owned. Prior300-scope accounting above is historical. First expected cost: observation fold. Owned client range updated only; shared launch infrastructure unchanged.

L302 passes LIBB_ObservationPieces: exact SAME-record ordered expansion, including failing C04 detail prefixes; all four own lemmas print standard axioms only. Source-only Piece/Pieces/Prefix definitions contain no native execution image. L301 failed on a theorem name and dependent elimination; replacement isolates the generic indexed-detail lemma before record elimination. Raw audits follow after the full fold. This support is not module12 completion.

L305/L309 pass the complete source observation model and parser/common native fold (LIBB_ObservationModel / LIBB_ObservationFold.tx2), retaining independently stopped C04 prefixes. Full-law Returns reuses LIBB_EnvValues; reservation binding is only the SAME reached records, not an own-input clause. All12 new roots print standard axioms. Native unfolding was factored generically to avoid Lean dependent-elimination failure; commonExit is an independent projection. L303/L304/L306–L308 are excluded elaboration failures, not accepted axioms evidence. Pure source law has no native-image definition. Whole-Obs Functional is distinct from full-law returned-value uniqueness; the frozen comment exempts infallible abort arms, and the interpretation question remains pending. Nothing is yet marked module12 DONE. Merged TX1 bundle objects copied byte-for-byte, hashes in LIBB_BUNDLE_REUSE.json.
