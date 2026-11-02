# NEN authoritative ledger handoff

**88/587 composed inventory occurrences CLOSED; 499 OPEN. Target not yet established.**
TX1: 44/345 CLOSED. TX2: 44/242 CLOSED. Canonical union: 44/434 unique functions CLOSED.
Contributing slices: Q 66, S 22. Overlapping membership: Q 66, S 24; the two Q `WideExact::to_limbs` occurrences also belong to S and are counted only once globally. No slice root is CLOSED: {'Q': [], 'S': []}.

## Exact established claim

`NEN_LEDGER.json` is the authoritative refresh of `NDT_LEDGER.json`, retaining all original inventories, statements, receipt history, body pins, trust rows and qualifications. `NEN_validate.py` invokes unchanged NDT/NCZ invariants on the immutable baseline, unchanged NEB row/edge certificates, and the unchanged NDT→NED→NEE→NEJ→NEL composition chain. It adds per-credit K-3/K-2 checks and active-dependency denial propagation. `NEN_LEDGER.md` lists every occurrence's admission/rejection reason; JSON lists each credit, native support and packet disposition.

Actual predecessor validator CLOSED counts: NEB 66, NEE 6, NEJ 14, NEL 22. **Zero slice-validator CLOSED rows are rejected by the unified validator.** Each earlier validator's occurrence list is retained explicitly. NEJ's stale six-row packet headline is not used instead of its actual fourteen-row result.

Candidate receipt K-3 inventory: RESTORED 143, UNAFFECTED 211, SUSPENDED 511, OPEN 221 (1,086 receipts including historical controls/incomplete attempts; this is not a count of independent theorems). All 315 claim records have a K-3 status. Historical admission flags remain separately visible; effective and authoritative admission flags deny suspended, unknown or quarantined support. K-2 harnesses remain named in `quarantine` and `NEN_credits` and provide no support even when their K-3 status would otherwise clear.

NEA's point/line claims are admitted through NEB's exact geometry certificates. Its separate constructor proposal is retained with OPEN support qualifications. Both NEC leaf proposals clear K-3, but no unified same-call/root certificate selects them; they receive no new composed credit. NEG's repaired local-record windows are checked with their failing controls; its historical K003/K009 remain suspended and its CLOSED member list remains empty. NEF's exact frozen None-observer source certificate is checked as a pure function; it supplies no full query/inverse bridge and does not lift K-2.

## Assumptions and scope

No cryptographic assumption, protocol parameter, frozen implementation, failure event, carrier, source-level domain or release target changed. No new assumption was discharged or introduced. P6/D188 option A remains native semantic-transport/tool trust reclassification; RuntimePersistence, source/ABI/allocator/ELF interpretation, the existing runtime trust rows, privacy, two-transaction obligations and the 100-bit per-attempt contract remain. Local conditional bridges are not whole-program or headline security closure.

Frozen implementation: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Merged input snapshot: `78c98c98a9d120157637aa656952705853c59d3b`. The 5,172 current top-level reports and all requested lane inputs are Git-pinned in `NEN_INPUTS.json`; changing the corpus requires an explicit refresh. Changed C3-BIN history is represented by both old and current hashes, never by relabelling an old receipt. A documentary mention supplies no automatic credit.

## Validation actually run and reused

- 53 original NDT mutation/invariant checks passed unchanged. Only their output receipt destination was redirected to this directory; predecessor files were not written. `NEN_NDT_TESTS.json`: exit 0, 11.918121 seconds, sampled aggregate RSS 1,557,954,560 bytes.
- 19 final unified mutation checks passed, including missing/wrong certificates, ruling y-prime after reviewed-content mutation, suspended K-3 transitive support, K-2 despite RESTORED K-3, failed formal assembly and failed nibble control. `NEN_TESTS_FINAL.json`: exit 0, 74.582089 seconds, sampled aggregate RSS 384,139,264 bytes.
- Generated ledger and Markdown compare byte-for-byte against a fresh recomputation. `NEN_FINAL.json`: exit 0, 32.982137 seconds, sampled aggregate RSS 1,043,890,176 bytes; exact validator source revision `41b6d7820118dbc762d4ba3d160a8b46d588c278`. SHA256 for each Python source is in that receipt.
- The complete original NDT successful replay is **reused**, bound by its receipt's ledger/validator/source hashes. This job rechecks every baseline artifact hash, every frozen whole-body slice and all original structural invariants. It does not claim a new historical collector/prover replay. All Lean axioms audits are read from pinned receipts, restricted by the original certificate gates to propext/Classical.choice/Quot.sound; no new theorem or axioms audit ran.
- 0 Lean, 0 Kani, 0 native/SBF builds and no remote-host or wallet/key operations. Python aggregate RSS watchdog: 7 GiB, 0.5-second samples. Linux additionally uses RLIMIT_AS; Darwin rejected AS/DATA caps before validation. Python swap was not measured; no prover resource result is asserted. Final data file is below 20 MB.

The initial unwrapped development failures and unavailable metrics, all later failed input/schema checks, and their replacements remain in `NEN_ATTEMPTS.jsonl`, logs and `NEN_DEVELOPMENT_FINDINGS.md`. No failed/timeout attempt provides proof credit. The final comparison is the first committed-source comparison of generated artifacts, not a repeated unchanged prover/package regression.

## Next concrete deliverables

499 occurrence obligations remain OPEN. Complete source-to-model/native-step associations and caller-owned packet-domain, carrier, same-input/state/full-Result and ordered-effect certificates; restore each actively needed suspended credit with the same original property/names, local records and matched failing controls. For S, the immediate continuation is the actual Enumerate/digest cursor and full common/payment child and byte frames (including rejection prefixes) identified in NEL_HANDOFF. For Q, complete the missing loop/native-emitted/callee-domain laws identified in NEG_HANDOFF and full None-specialised query/inverse bridges without lifting historical K-2 quarantine. Independent local results and source certificates cannot replace these obligations.

## Repository disposition

Actual existing branch retained: `codex/cx-ledger4-20261102` (brief named `codex/cx-ledger4-20261029`). Stage 1 commit `bc550c8bb8`; stage 2 commit `41b6d78201`; stage 3 commits the authoritative artifacts and this handoff. Nothing pushed. Changes are confined to `evidence/ledger4-20261102/`; predecessor modules and shipped crates/programs are unchanged. No ELF rebuild trigger occurred, and inherited artifact pins were not reproduced.

Reproduce the final comparison with:

```
python3 evidence/ledger4-20261102/NEN_validate.py
```

Use `NEN_run.py <receipt-name> <python-target> [args...]` when a fresh Python receipt is required. Rerun only for a source/input change or specifically missing evidence; no Lean or Kani is authorized by this handoff.
