# Resume checkpoint

Rust source repair ccf87ccecd; runtime source frozen since then. weights.rs
byte-equals c57a344726 (sha ab55509e…); only two direct host powers calls
redirect to cfg(prover) prover_powers. Seven runtime files +46/-9 vs c57.
MODULE-GATES.md and revised-applied.diff name every module gate.

Gate(a) all three exact pins pass: default41.435s/686356KiB, devnet50.679s/
685640KiB, Pool39.930s/678204KiB; exits0,swaps0,sourceccf87ccecd.
Fresh extraction all230/254/258 passed unchanged pinned Charon/Aeneas;
raw outputs retained; backend-ports.json records only import and shift ports.
No shared env-J source write. Task-private source/object roots; private env
preserves shared J/objects namespace priority after private objects.

Checked standalone source laws:
- PV_B1_SumOriginal.op230_source (53629), all raw inputs, exact Option guard
  and ordered native CT fold; control/native fold bridges also checked.
- PV_B1_PowersControl.op254_source (53621), arbitrary-N complete Result;
  PV_B1_PowersBridge.op254_copy_equal_original (53634), original early-return
  representation bound structurally to actual extracted constants/mul.
- PV_B1_PoleControl.op258_source (53632), arbitrary-input complete Result;
  PV_B1_PoleBridge.op258_source (53645), equality to predecessor flat
  original-verdict representation; byte bindings/provenance explicit.
- Shift literal4/31, masked usize→U32 cast exactness and lift nonfailure
  checked53603–53605; bit/block bounds checked, no narrowed input domain.

Reference pole classification and full truth law port passed53648–53663;
private callback signature cohort passed53664–53666; carrier bijections
passed53667–53670. All successful axiom queries standard only. Model/native
association and native effects remain distinct. Endpoint premises removed0;
T remains exactly entropy_law/entropy_kernel/observation. Target not established.

Budget currently67/100 charged; Kani0/0. Next unused53671; IDs53627,53628,
53647,53659 refused before scopes (charged0); never reuse. Audit53897–53899
untouched. TALLY.json is authoritative. One scope at a time. No active own
scope at this checkpoint.

Native recommended devnet_spend build passed:112.857s,642240KiB,swap0.
Example build passed43.186s,565996KiB,swap0. Two whole-prover fixtures passed
runtime37.580s,666428KiB,swap0. Fixture comparison passed: public/proof/ledger
bytes and all result fields except diagnostic seconds equal for transfer0
and withdrawal0. Baseline files from37794d7bff have pinned public/proof hashes
and no runtime/config diff vs c57a344726; see fixture-baseline-binding.json.
No saved failure case exists; both statuses are Ok; failure status would be
compared if present. No quiet-host performance claim or1,000-run claim.

Pending local proof files (uncompiled): FieldCTTotal,FieldM31Total,
FieldCM31Total,FieldQM31Total,FieldWideTotal,PowersTotal,PoleOutcome,Install,
InstallStability,ReferenceInstall,CarrierContainers. Need commit/stage and
focused checks, then strengthen typed row output/transport as budget allows,
complete three reserved audits, collect receipts and write final report.
Native/fixture build receipts and comparison JSON collected by collect.py.
Root fixture-comparison-receipt, later lean-receipts (after53612), private
launcher/env snapshots still need fresh-admission collection. Most recent
collection refusal: reservation-proof-fixture-collect.json on host; obey180s.

Private host H=/home/dombarker/project-offloads/codex-pv-batch1-20261027.
lean.py invokes private-root derivative of standing launcher; source and
proof revisions separated. compile-local.py tallies IDs/charged attempts
and stops on rejection. For changed source: path-limited commit, fresh
admission, scp only new/changed PV_B1_ files, update H/proof-revision.txt to
commit hash, then compile-local.py modules in dependency order. Failed
sources are not accepted (compiler-produced sorryAx logs retained as rejected).

Native build label initially collided with SBF build-devnet-prover-local;
no scope started; corrected fresh label build-native-devnet-prover-local.
Earlier four-second-early reservation retry is recorded in RESUME.md.
Keys retained securely; no key cleanup, fund movement, RPC send or push.
