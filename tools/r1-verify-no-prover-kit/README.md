# No-prover verify/query/counter plan — NOT RUN

Ten declared test/tool overlay files extend the accepted saved-S2 gates. Source
revision234a1431ba0ec533261864b6d34c86997c70239d is required by the current pins;
production inputs match accepted6dd byte-for-byte. `prepare.py --after REF` checks
the relevant production files and emits complete before/after diffs;
`--stage DIR` writes only the declared snapshot files, never a production worktree.
The strict full-input staging audit (532 Git-exact files including2 fixtures) additionally compares every retained source/fixture
file to Git234 and admits only these10 overlay paths plus pinned fixtures.

Four optimized native commands are pinned in source-pins.json:

| Gate | CLI features | Required actual cost-probe rustc features | Cases |
|---|---|---|---|
| verify-no-prover-default | private-leaf-salts,optimized-terminal | default,optimized-terminal,private-leaf-salts | 112 |
| verify-no-prover-detail | preceding +detail-phases | default,detail-phases,optimized-terminal,private-leaf-salts | 112 |
| query-no-prover-102 | private-leaf-salts,optimized-terminal | default,optimized-terminal,private-leaf-salts | 102 |
| counter-no-prover-583 | none on CLI; dependency private-leaf-salts | default,private-leaf-salts | 583 calls:349/234 |

The three injection builds retain the empty cost-probe default feature. The
standalone counter also enables empty defaults through its dependency. Neither
prover nor an aspis_prover extern is permitted in the actual cost-probe compiler
invocation. A Cargo.lock package record alone does not indicate an enabled crate.
Checkpoint23 already has accepted no-prover compiler evidence and is not rerun.
Codec is a statement codec gate and does not compile cost-probe.

Verify changes remove prover from old-body/test-module guards, make only the
three diagnostic returned fields conditional, expose std under cfg(test), and
add SHA/JSON as dev-dependencies. The actual statement_public declaration/body
is copied byte-exact into the harness, so no prover dependency is needed. All
55 symmetric faults, success controls, deployed-shape returned fields, real
digest calls, events, errors and both observer modes/phases remain compared.

Query changes remove prover only from test selection, retain exact old/new query
bodies, all102 contexts/faults,17 digest input/answer events, decoder inputs/results,
carried state and all22 returned queries. The fixture/context remains exact.
Counter changes copy only actual host_hashv and statement_public declarations /
bodies byte-exact, remove aspis_prover and cost-probe/prover from the test tool
manifest, and update only that dependency edge in the tool lockfile. Real tx1/tx2,
all583 ordered digest calls,349/234 phase counts, checkpoint bytes and acceptance
must match the saved baseline.

**No-prover trace-value limitation:** production trace::value is compiled to a
no-op and trace::take is unavailable. The snapshot helper therefore returns an
empty Vec and every injection comparison explicitly asserts empty values. This
does not establish the prover-only value log under deployment features. Actual
digest calls/errors/events, returned fields and observer phases are still
compared; no test hook enables recording or changes deployed arithmetic. Each
injection test rejects cfg(prover). Synthetic wrapper failures remain explicitly
test-only; saved-S2 success is actual fixture execution, synthetic query S1/D
contexts are not claimed to be valid saved proofs.

The user override "just do it in parallel" permits A/B overlap and foreign Lean
activity when aggregate reservations fit. A native command still requires the
coordinator's B-window grant. `governor.py` defaults to dry preflight, acquires
the B-specific `/tmp/aspis-r1-worker-b-native.lock` nonblocking, and records foreign
Lean/compiler/replay activity without blocking or signalling it. Exact own-scope
matching distinguishes reparented own children from foreign same-user jobs; it
never exempts a broad user prefix. Pure fixtures test that classification.

The native child requires a dedicated scope with MemoryHigh6G/MemoryMax8G /
MemorySwapMax0. Admission sums all populated finite-cgroup MemoryMax reservations (including services)
(including A/foreign scopes), adds B's8GiB once, and requires <=55GiB immediately
before launch and continuously during the job. Only an unsafe aggregate or own
timeout may stop B's own process group; foreign arrival alone never does. The
receipt pins this user override, reservations, foreign activity and cgroup
peak/swap/events even if the inner runner cannot finish its receipt. Four B
commands run sequentially with a private copied cache and immutable manifests.

run-host.py is byte-identical to accepted SHA
d011230e71adac99208489591e770e92744e53f9117be18060e315770866bb8c.
It records exact command/exit/wall/RSS/swap/revision/caps. `check-expanded.py`
requires actual archived rustc cfg/extern evidence, full executed case counts,
nonzero one-passed-test result, exact source revision and gate-specific equality.
If the query gate executes the same cached binary as verify-default, it requires
that binary's exact successful producer receipt, same immutable input manifest,
matching executed artifact hash and actual producer rustc cfg. A bare `Fresh`
line or CLI feature flag does not establish resolved features. The counter check
also requires exact saved ordered-call and checkpoint comparison. No SBF build,
readonly runtime harness, proof generation or Lean job belongs to this kit.

Accepted results are now in `evidence/native-no-prover-20261018` under the research
path. The three injection gates retain their frozen ten-file snapshot and pins
in `source-pins-injections-accepted.json`; unused counter tool overlays did not
participate in those three tests. The accepted counter uses a SEPARATE clean
532-file baseline with ONLY3 counter tool overlays, recorded by
`source-pins-counter-accepted.json`. Running the counter against the injection
snapshot is invalid (test wrappers are cfg(test)-only); that rejected compilation
is retained. Never use the injection snapshot for the normal-library counter.

The current reproducible `source-pins.json` is counter-only: prepare with
`--scope counter`. Its3 overlay byte hashes and command are identical to accepted
counter pins. Canonical lock text is stored inside `counter-lock-refresh.json`;
only unused prover packages/edges were pruned, with retained versions/sources /
checksums unchanged. `source-pin-maintenance.json` records the packaging-only
loader change; no native rerun followed it. The final packet is JSON/logs/SHA
manifests only and includes all native failures and the checker-prefix correction.
