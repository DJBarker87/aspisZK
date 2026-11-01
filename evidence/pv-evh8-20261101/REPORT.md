# EVH8 resumed prover event work — target not yet established

Branch `codex/pv-evh-20261029`; worktree `/Users/dominic/ZK/.worktrees/pv-evh`.
Baseline `0da088f6f87a20db01518eb53c95e2343f7b47bf` (D545).
**Rows removed: NONE.** No privacy endpoint premise or trust field changed.

The accepted opening source chain replaces LeafInstall's three whole opening
helpers with `PrepareOpening.run`, `FinishOpening.run` and `PublishCompact.run`,
installed by `OpeningInstall.install_fixed` and composed through
`OpeningProver.entry_fixed` into the actual extracted
`RealR1_client.prove_for_proof_accounts` source. This remains local Result
transport on the compatible finished domain. It is not full native event
coverage or an actual successful entry witness.

`PublishCompact` explicitly interprets the source `Vec.with_capacity` let as an
effect-capable callee. The pure source value's compatibility is a separate
premise; native allocation failure is not silently dropped or declared equal
to source success. `ValueBind.value_bind_fixed` proves the required symbolic
transport law, with no axioms. The generator preserves this transformation.
All thirteen Result-returning publication callees, the capacity leaf, and all
sixteen preparation/thirteen completion callees retain native obligations.

The source entropy nonzero loop is interpreted through `NonzeroStep` and
`NonzeroFlow`, with no whole nonzero-helper answer. It is installed at both
inner entropy-block checks and the outer mask-nonce guard by `NonzeroInstall`
and `NonzeroProver` (focused compilation status in receipts). Private-salt
step/loop source spines and their entry installation are also prepared.
Native primitive safety and adequate finite fuel are separate checks; no
exhaustion is counted as source divergence or successful completion.

Every host invocation is one module under 6G high / 8G max / swap0 / tasks64,
Lean -M7000, and same-shell admission requires exit zero plus allowed:true.
Receipts give target, exact revision/blob/SHA, dependency fingerprint, exit,
wall, RSS, swap and all printed axioms. Historical restoration was established
from the committed flag record and D540 resume; the temporary flag was already
absent in D540. `restoration-resolution.json` records the evidence. No host
bootstrap or infrastructure edits were made. The new wrapper changes assigned
range/audit threshold, receipt destination and inherited receipt/cache inputs.

Reservation refusals are uncharged and retain the same ID after a full
180-second cooldown. Source failures are retained and never rerun unchanged:
79307 lacked an explicit tuple state; 79308 then needed tuple projections
normalized before the source loop case split; 79309 is its accepted replacement.
No memory kill or limit increase occurred.

The remaining work is native leaf installation (heap/address/failure, drop and
zeroization, formatting, hash/query bytes, and source primitive associations),
then full prover trace equality for unchanged oraclePrefix/countTrace and the
nonce-store fileTrace projection. D520/U/D524 client inputs remain named.
Only after those actual-family links are proved may (v') reduce consistency to
a successful worldRun at runjoin's opsNative and allocator world. No such
reduction, full manifest replay, native run or Kani run is claimed here.

## Native operator correction and current focused evidence

The actual loaded Result.map/map_err declarations alias ExternalFuns.op11/op12.
They are not automatically certified language primitives. native-preflight.json
identifies seven lifted sites; native_preflight.py --check reproduces the census
and --require-native-closure fails while they remain. This strengthens the
explicit native frontier; it changes no accepted Result-transport statement.
Callback/drop and actual dictionary association must be proved in addition to
all named Compatible fields. ResultOps and PrivateSaltWrap are drafted to expose
these operations, not credited as actual opsNative installations.

NonzeroSafety (79319) is accepted: checked read bound, non-wrapping increment,
step totality and exact equality of the interpreted step to its checked-value
source. NonzeroTotal is not yet accepted: the source changes isolate PrefixLoop's
terminal equation and expose the final concrete bind, with no increased limits.
PrivateSaltStep/PrivateSaltsStep are accepted at 79314/79317; the flow/entry
consumers remain uncompiled. The strongest accepted entry is NonzeroProver.

Read-only audit PASS at this snapshot: 23 charged attempts, 14 accepted, nine
failed, 57 attempts remaining. Next fresh ID 79323 is refused and UNCHARGED;
a full 180-second cooldown precedes same-ID retry. Audits 79397–79399 untouched.
Every accepted source and object/receipt hash reconciles with the retained host;
there is no live owned scope. No full release replay was run.
