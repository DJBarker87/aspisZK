READY-AGG (D595). No 16 GiB admission requested or scope launched. ID 92060 is spent (failed); ID 92070 is spent (successful preflight). A fresh ID and Stream A admission are the lead's next action, outside this job's authorization.

Driver form: adapted copy of research `evidence/axaudit2-20261102/NEP_Driver.lean`, changing ONLY module names and root names; see the full `DRIVER.diff`. Its hardcoded root lists prevent using the unchanged driver through arguments or an import-only wrapper. `NEP_WALKER.lean` is byte-identical to research. No audited module changed. The preflight used this exact driver and walker.

On the host, define:

```sh
D=/home/dombarker/project-offloads/codex-pv-evhc9-20261104
P=/home/dombarker/project-offloads/codex-pv-evhc8-20261104
O=/home/dombarker/project-offloads/codex-pv-evhc6-20261103/objects
L=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake
export LEAN_PATH="$D:$O:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean"
```

The exact three-step command sequence, run in one fresh output directory in ONE admitted scope, is:

```sh
"$L" env lean -j1 -M15000 -DElab.async=false -o "$O/PV_BR_FixtureConsumer.olean" PV_BR_FixtureConsumer.lean
"$L" env lean -j1 -M15000 -DElab.async=false --run PV_NER_Scan.lean
"$L" env lean -j1 -M15000 -DElab.async=false --run "$D/NEP_Driver.lean" final
```

`AGG-SEQUENCE.py` implements that sequence with the unchanged evhc8 validation, separate logs/timing, a 600-second timeout per step, and first-failure stop. It copies unchanged consumer/scanner/manifest inputs into the fresh output directory, rechecks every combined-object pin before step 1, requires the exact 16,539-module scan with zero dangling references and matching imports, and checks all 32 raw results. It requires both soundness roots' counts, edges and axioms to match `NER_AXIOMS.json` exactly (115,256 and 885,736 constants; standard axioms only). It creates no scope and performs no admission.

Future runner configuration: kind `lean`, fresh attempt `lean-<LEAD-ID>`, command `['python3', D+'/AGG-SEQUENCE.py', D+'/agg-<LEAD-ID>', '<committed-revision>']`, timeout 1850, the LEAN_PATH above, source snapshots including `AGG-SEQUENCE.py`, driver, walker, DRIVER.diff, and all unchanged inputs consumed from P. Record their hashes, the compiled walker pin from `POST-PREFLIGHT-HOST.log`, and source revision. Hash-check the whole unchanged combined closure against `ALL-OBJECT-HASH-CHECKS.json`, all NER cohort/companion and rebuilt pins before admission, and ensure all source inputs still match committed hashes. Do not reuse or overwrite evhc8 output receipts.

Only after the lead authorizes the scope: verify the lead-owned runner hashes from evhc8 `PREFLIGHT.json` (full hashes; prefixes d6d40da5, 9b325ab0, 8165ccff), run `reservation_agg16.py` with a retained receipt, require BOTH exit 0 and allowed:true, and on exit 78/allowed:false wait 180 seconds, at most 20 admission checks. No bypass. Execute the configuration ONCE:

```sh
systemd-run --user --scope --quiet --unit="pv-evhc-<LEAD-ID>" \
  -p MemoryHigh=14G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 "$P/S2W_run_host_agg16.py" '<config-in-P>.json'
```

That existing runner accepts the explicit command and records resources, source snapshots and revision. Its configuration and sources must be staged under P (runner base) with fresh names; the output directory passed to AGG-SEQUENCE must not exist. No retry or cap change on any failed step. The lead must collect complete raw results and full reachable lists, not only summary-based `#print axioms` output.

No privacy premise was removed, added or changed. FixturePdaRuntime base, event-acquisition and joint-simulation obligations remain. Privacy target not yet established; full combined composition remains unaudited until the future three steps all pass.
