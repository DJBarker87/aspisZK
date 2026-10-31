# Resume checkpoint after session 1 continuation

Task incomplete; do not treat this as a release. Read original prompt-pv-uc.txt and pv-common.txt again as necessary, REPORT.md, attempts.json and DESIGN.md. Only writer, exact worktree `/Users/dominic/ZK/.worktrees/pv-uc`, branch `codex/pv-uc-20261029`, base `683e01efee`. Never edit other checkouts, merge, push or repin. Never access deployment authority keys. All gates offline except SSH transport to the dedicated build host.

## Durable state

- Native N75100–N75131 consumed, 32/50 scopes, 18 left. Next N75132 (do not reuse any ID). Lean zero of 40, next 75000. Kani zero permitted.
- All 32 host done statuses recovered; latest host checkpoint: only init.scope live. Check again before launching. Do not resubmit a pending scope after an SSH failure.
- Host workspace `/home/dombarker/project-offloads/codex-pv-uc-20261029`, SSH `dombarker@100.108.41.90`. Reuse its existing src/native-target/charon-target and exact files. No need to restage whole workspace or recreate fixtures.
- `tools/pv-uc-20261029/scope.py` uses existing shared reservation/barrier, AND checks admission exit and allowed:true, detached one-shot launch plus done-status polling. Caps 6G/8G/swap0/TasksMax64. Sequential only. Barrier refusal: preserve ID, 180-second cooldown, next unused ID; no bypass. Existing wrapper enforces cooldown over recorded refusals. No infrastructure changes.
- `summarize.py` verifies receipts/resource caps/time exits and fixture source identity, writes attempts.json/source-boundaries.json. No Lean has run; if starting Lean, extend this summary to count actual Lean receipts instead of leaving hardcoded zero.

## Exact current extraction issue

Charon passes with has_errors=false on the current source. `charon.json` records flags, opaque boundaries and exact host path. `extract.py` verifies Charon and accepted ae1-2 Aeneas hashes. `pipeline.py outputNNNNN` runs extract then translate; each destination must be fresh.

N75130: Aeneas crashes `Not_found` in `InterpReduceCollapse.collapse_ctx_following_sequence` line 1991 (17.94 s, 2,638,500 KiB, zero swap).
N75131 uses `translate-diagnostic.py output75131` (same LLBC, new Translate logging): isolates the failing declaration as **user_client::membership::input** (15.00 s, 2,728,480 KiB, zero swap). Full log 219KB under native75131. No tool, LLBC or emission edited. Host checkpoint pins current LLBC and config hashes. Need NOT rerun unchanged diagnostics.

Next source action: split membership::input into small Result helpers for public preparation, roots collection, selection and final super-root witness construction. The likely bad join combines `selected: Option<(lane,pair,index,second,siblings)>` branches with a borrowed prepared Vec. Move branches into small pure helpers; preserve behavior and full-lane non-selective scanning. Do not make input or plan::prove opaque to get a pass. Preserve no ?/early return inside nested loops and no mutable captures across fallible calls. Capture public nonce keys by value (Accounts Copy, move callback) was necessary to pass the earlier RealR1 boundary refusal.

After editing, commit source, scp ONLY changed files to matching host src paths and any own extraction configuration changes, then:

```
python3 tools/pv-uc-20261029/scope.py native75132 extraction-and-translation \
  python3 /home/dombarker/project-offloads/codex-pv-uc-20261029/pipeline.py output75132
```

Do not alter translators. Their identities and open helper opacity are in REPORT. Merely completing translation is insufficient: external templates contain axioms; filling them with axioms/sorry is not the standard-axioms gate. D188 restoration fidelity must also be checked for generated functions before credit. New Lean attempts must follow object-authority/cohort resolution and exact receipt/axiom rules; no full replay before focused files/bridge/audit pass.

## Validation status

N75121 built all three native targets with Rust 1.94.1 client profile and ran real transfer/withdrawal user proofs from fixture bytes through inherited pipes. Both exit0, stderr empty. This predates subsequent source changes. `preflight-build.py` writes fixed `preflight/` with exist_ok=False: do not rerun unchanged or reuse that output path. If a later focused functional check is justified by changed source, give it a fresh explicitly named output directory and a new ID. Existing recovery data/ledgers must be retained.

No FINAL gate has run: no three-ELF rebuild, 1,000-pair user-vs-fixture statement/proof-input/instruction comparison, own D359(A) timing, optimized decoder instruction trace, Types/Funs compile/standard axioms, final SHA. Do not repeat pv-c474c combined-client timing. Timing baseline is shipped `30d883a8…`, not the combined intermediate. Quiet marker is expired and must not be edited/deleted; normal admission allowed under e'.

Fixture harness source remains byte-for-byte base. `source-boundaries.json` hashes it; crates/programs untouched. Its SDK path built, but N75121's newly built harness SHA differs from historical bundle artifact; report does not claim artifact identity. The accepted prior harness/control artifacts remain on host read-only. Final client binary not frozen: N75121 hash is explicitly intermediate.

Private/public table and pending obligations are in REPORT. No privacy premise removed; no T field added. Target not established. Unproved native-I/O/public JSON/hash-selection helper associations remain P obligations, not trust items. Preserve all wallet keys/recovery/nonce ledgers and do not clean caches needed for continuation. Before ending another context, collect every live host run and commit updated receipts, REPORT and this handoff.
