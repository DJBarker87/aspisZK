# PoolL handoff — budgets exhausted; exhaustive target not established

Branch `codex/cx-pool-nonint3-20261026`, own worktree only. All commits local;
no push. Resume anchor `e901689195`, original freeze `efdf70b17f`. No concrete
accepted write of attacker-chosen checkpoint bytes was found. The requested
universal handler frames and `PoolL_Frame.all_handlers` are NOT proved.

## Established claims and their exact scope

`PoolL_AllocateAccepted.accepted` now compiles (020 replaces019's redundant
solved-goal tactic). `PoolL_PayerAccepted.accepted` also needed a separate
non-progress simp correction (021 replaces018). Original failed receipts remain.

Native small cuts were extracted with Charon/Aeneas, installed on the canonical
PoolM/Hiq SDK metadata carrier, and checked in Lean. Program/Fresh/Marker/Vault/
Canonical sources preserve actual owner/key/flag checks and error ordering.
BorrowSource/BorrowFacts preserve the native Try/Result borrow-error path.
CanonicalRole, FreshRole and MarkerRole stop at the first type/length guard;
zero scan, decoding and arithmetic suffixes are not assumed to succeed. Their
control/rejection/effect proofs retain arbitrary supplied prior state and the
complete ordered prior log. Close and allocation cuts block every later
close/refund/tombstone/resize/assign/create/top-up/WithSeed/CPI suffix on rejection.
This does not derive earlier effects or their physical checkpoint frame.

`PoolL_Physical` constructs one key-indexed observation cut: metadata key,
data, SDK length and emptiness share that key. PhysicalCanonical/Fresh/Marker/
Allocate/Close/Plan prove local exclusions on this SAME observation, and
PhysicalAlias proves coherent alias reads. This is a constructed cut, NOT the
missing native runtime-to-cut interpretation. No independently chosen length
Result is a premise of these physical-cut corollaries.

`PoolL_CancelPhysical.accepted_separation` inverts the inherited AENEAS005
native ASPX role cut: acceptance separates an occupied key from core, optional
shard and refund authority (checkpoint owner is explicitly non-System).
`PoolL_ASPXRoles.role_frame` handles every selected role position with arbitrary
prior Result/state/log. Actual parser/count/unique/index/SDK selection, the
whole suffix footprints and their SAME native execution still need binding.

The eleven `PoolL_*Roles.role_frame` statements name individual live-handler
cuts, not complete handlers. Their comments and full statements explicitly
retain the missing source account-selection and execution interpretation.
`before` is a prior child Result; supplied state/log are pre-cut observations,
not an assertion that the earlier handler had no effects. In particular AS8D
and ASPP are not reordered before their arithmetic or earlier CPI.

Header success branches and three owned role success branches are constructed
in *Reach modules. These establish local non-vacuity, not authenticated native
whole-handler reachability. `PoolL_VerifierScopes` retains the inherited actual
V1 zero-gate and accepted V2 whole-heap wrapper boundaries; it does not newly
instantiate release admission, native SDK representations or source-to-ELF.

## Native Kani evidence

| Runs | Actual checked domain |
|---|---|
|001/002|Literal FULL native close helper; arbitrary192/1768 bytes, keys, flags, balances and byte index; both10000/8504 plan widths; exact error and full pointwise byte/balance frame.|
|003/004|Literal FULL freshness helper; arbitrary192/1768 account and six destination widths384/768/1000/8256/10000/8504; exact error/frame; cover reaches native borrow/length guard.|
|006/007|FULL freshness native error equals extracted owned role error on the SAME AccountInfo, actual borrow bytes, emptiness and System ID; both widths, full frame and reached guard cover.|
|008/009|Canonical-state native metadata/borrow/length prefix equals extracted role on SAME192/1768 SDK fixture; full frame, native length guard reached.|
|010/011|Marker native flags/owner/borrow/length prefix equals extracted role on SAME192/1768 fixture; exact marker error/full frame/reached guard. Zero/decoder suffix excluded by length.|
|012/013|Actual common allocation prefix with payer/System and owner/empty checks rejects both nonempty widths; arbitrary metadata/data/balance/index, full frame. Covers only metadata shapes, not proof of reaching the final guard past a valid payer/System pair.|

All fixtures use real SDK AccountInfo with free borrows and arbitrary scalar
metadata; they do not quantify arbitrary SDK representations, enclosing account
lists, caller arithmetic or all runtime executions. Rust copies/prefix cuts
are retained as source evidence; no shipped cfg(kani) file was changed.

005 failed Rust compilation on a moved Result, repaired using borrowed error
projections in006.014 stack guard TIMED OUT at60s; no unchanged retry.015 CPI
meta probe failed an unwinding assertion in builtin memcmp (bound9 versus the
32-byte key comparison), leaving406 checks undetermined and cover unestablished.
These are not accepted writes or source security counterexamples. The full
stack/dispatcher and native CPI builder/invoke join remain open; use scoped
predecessor evidence only within its original domains.

## Per-handler universal deliverable status

“Open” means the requested complete accepted execution/physical-account frame
is not proved, even where a named local role cut compiles.

| Handler | Status | Checked local predecessor / missing universal join |
|---|---|---|
|AS8I|OPEN|384/768 fresh cuts; all14-account selection, vault, allocation and CPI footprints remain.|
|AS8C|OPEN, kernel owned by PoolW|Our384 master data cut only. Occupied192 kernel freshness/origin is not claimed here.|
|AS8D|OPEN|768/8256 type cuts; actual lane/address/arithmetic/page/token and mutation joins remain.|
|ASQ8|OPEN|Marker cut; readonly ASC8/CP, lane/pages, full verifier/System/SPL invocation and layout joins remain.|
|ASIN|OPEN|1000/8256 fresh cuts; full seven-account selection, vault and creation/write joins remain.|
|ASDI|OPEN|Canonical primary-state cut, generalized native fixture; current/rollover/token roles and full handler join remain.|
|ASPP|OPEN|10000/8504 fresh cuts preserve earlier cut effects; plan construction, rollover page/CPI and all account joins remain.|
|ASPX|OPEN|All selected native role positions excluded at cut, physical close guards; full parser/unique/SDK/suffix instance remains.|
|ASPF|OPEN|10000/8504 close guards and canonical predecessor; complete state/page/marker/token/receipt/close instance remains.|
|ASPT|OPEN|Canonical primary-state cut; all page/marker/readonly-verifier and actual suffix footprints remain.|
|ASWD|OPEN|Canonical primary-state cut; pages/marker/token/withdrawal CPI and full source execution remain.|
|Verifier V1|OPEN for requested release instance|Inherited occupied source rejection; actual admission/physical SDK/runtime/ELF joins retain their original boundaries.|
|Verifier V2|OPEN for requested release instance|Inherited accepted whole-heap frame, arbitrary observation corollary; actual admission/CPI/runtime/ELF joins remain.|
|Pool dispatcher|OPEN|Literal stack probe014 timed out; exhaustive branch/body/effect/physical instance remains.|
|PoolL_Frame.all_handlers|OPEN|Not declared. No conjunction assuming missing handler frames is offered as closure.|

No new trust item, metric, adversary restriction, security hypothesis or
whole-lifecycle/only-AS8C-writes premise was introduced. Retained: adopted SDK
borrow/TrustedStd boundaries, runtime ownership/CPI/syscall/rollback/alias rules,
fixed deployment/genesis, imported extraction/native/allocator boundaries and
source-to-ELF obligations. No global ledger row is removed;100-bit target is
not established. These local cuts do not discharge provenance or causality.

## Validation, resource receipts and stop

HARD STOP: Lean100/100 attempts, including resumed001–019 and final audit100;
81 pass/19 rejected elaborations. Kani15/15,12 pass/3 fail as above. No dependency
build or package/manifest replay. All81 current top theorems printed in one
final focused audit100, exit0,1.873326647s,peak4343396KiB,swap0; axioms only
propext/Classical.choice/Quot.sound (or subsets). Failed sorryAx outputs remain
raw rejected evidence, not accepted proofs. Generated external templates are
uncompiled extraction artifacts, not new axioms in compiled PoolL modules.

PoolL_attempts.jsonl and individual receipts contain exact command/target,
source hash/anchor/dirty overlay, selected object fingerprints, exit, wall,
peakRSS, swaps, cgroup caps and complete printed axioms/errors. Source revision
context corrections for copied extraction command templates are in
PoolL_REVISION_CONTEXT.json; original receipts are preserved unchanged.

Lean total191.19590758s,peak4446576KiB; Kani total133.89578538s,peak470520KiB;
all swaps0. Scopes6G high/8G max/swap0/tasks64, Lean-M7000; native Rust/Kani
optimized, four jobs. At most three independent Lean scopes together here;
other workers untouched. No cap increase, memory-killed rerun or timeout retry.
Existing S2W runners and coherent SInt2/Hist/Hiq/Hir/PoolN/PoolM objects reused;
no launcher/monitoring infrastructure modified. Final host inventory: no live
PoolL job (indeed only init.scope). No generated binaries/objects/ELFs committed.

PoolL_validate.py passed: every source snapshot hash,100/15 receipt accounting,
all current81 Lean module sources matched to green receipts,81-theorem axiom
audit, exact resource limits/swap, assigned diff scope, original source pins,
and all132/132/133 inherited release compiler inputs. It is an evidence audit,
not a semantic closure test. Source files, features, lock, keys/accounts/funds
and deployed artifacts unchanged. No SBF rebuild trigger. Inherited hashes,
NOT newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

## Next concrete deliverable

Finish one actual ASPX source-to-cut instance: reuse native role extraction,
prove parser/count/unique/selection on the physical account list, couple actual
SDK data_len/System observations, and attach the two close helper footprints
on that SAME execution. Then generalize every writable role/mutation/CPI in
the table with actual earlier cut effects preserved. Do not commission another
history wrapper or promote the constructed key-indexed cut into a runtime
instance. The requested exhaustive theorem remains the target, not these
partial role claims. No further proof run is authorized within this exhausted
budget.
