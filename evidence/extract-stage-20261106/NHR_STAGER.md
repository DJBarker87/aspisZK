# Frozen-workspace extraction stager

`NHR_stage.py` discovers the root manifest's workspace members (including glob
members), workspace dependencies, and every transitive path dependency in normal,
build, dev, target, patch and replace tables. It copies ALL tracked package files,
not a suffix-filtered source subset. Literal Rust include inputs outside package
roots are followed recursively. Sources come exclusively from Git objects at
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; no live worktree is read.

`--export` writes the committed compressed base64 payload and SHA256 manifest.
The host reconstructs it without requiring a Git checkout. Each file is checked
against both its SHA256 and its Git blob ID before staging. Existing drift is a
hard failure. No root manifest, frozen lock, crate or program is rewritten.

## Successor commands

From the repository, regenerate frozen transport inputs only when necessary:

```
python3 evidence/extract-stage-20261106/NHR_stage.py --export
```

Use `NHR_run.py` (a prefix-owned adaptation of NHA_run.py) to run configurations
through the unchanged SInt2 launcher. It records reservation stdout before any
upload and requires BOTH exit 0 and allowed:true. It never launches on refusal.
The existing capped scope is MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64. One scope at a time. Preflight, which launches no compiler/Charon:

```
python3 evidence/extract-stage-20261106/NHR_run.py NHR_P001
```

P001 is historical: do not rerun the immutable attempt ID. For a successor,
copy its JSON to a fresh prefix-owned ID, updating attempt and upload paths.
The command inside that scope is exactly:

```
python3 NHR_stage.py --check
```

It stages into NHR_workspace and runs Cargo +1.94.1 metadata --locked --offline
on the verifier manifest with default plus private-leaf-salts,optimized-terminal,
program-build. It records all resolved crate features and checks package keys
and every resolved edge against the frozen lock. Only the same three disabled
optional packages as NFQ/NFZ may be absent, guarded by the optional manifest flag
and absence of r1p-check. Added packages, edge drift or lock drift fail.

Each extraction is a separate admitted configuration whose command is:

```
python3 NHR_stage.py --extract --function prepare --out NHR_emitted/prepare
```

Replace prepare with tx1, tx2_authenticated or tx2_common. NHR_OPACITY.json is
explicit input: every path has a reason. `--options --function prepare` emits
exact commands without running tools. The option set is NHA's built MIR/aeneas
preset, explicit core Option/Result/ok_or, offline locked optimized single-job
Charon, then sequential diagnostic split Lean Aeneas. Executables are pinned
to daad69be… and c0cf4fcc…. Metadata and full source validation precede EVERY
extraction. Lock and sources are checked again afterward.

P001 passed: exit0,0.690695s,103796KiB RSS,swap0; receipt/admission/graph are
committed. No Lean theorem or native correspondence follows from this check.

Own-input repair before P001: the initial exporter treated `[lib].path` as a
crate dependency. The corrected traversal only interprets dependency/patch/
replace path fields, including those nested in workspace/target tables. No host
extraction or compile was consumed by that local failure.

## Opaque-call compilation interface

`NHR_parameterize.py FUNCTION --raw <relative-raw-output-directory>` creates
NHR_lean/NHR_FUNCTION. It preserves raw emissions separately. Aeneas external
axiom templates are NEVER compiled. Instead each external declaration's exact
type becomes an explicit section parameter, and calls are renamed to that
parameter in the emitted body. No callee implementation, success premise,
axiom or handwritten substitute body is supplied. Successors must instantiate
these parameters with their proven packets and establish nominal carrier/domain
association; that is not done by this job.

The Types compilation copy removes discriminant macro attributes to avoid
Aeneas's globally named instance collisions in NGK (same adaptation as NHA).
No types, constructors, control flow or function statements are removed. The
full generated-to-compilation diffs and external-signature map are committed.
Generated Aeneas heartbeat/depth settings are retained; none is added/raised.
Each compiled driver prints its actual axioms. No theorem is introduced.

NHR_L001/L002 compile prepare Types/Funs with the selected Aeneas objects pinned:
exit0/0,2.272386/1.834017s,2659716/2647652KiB RSS,swap0. The parameterized prepare
body prints exactly [propext, Classical.choice, Quot.sound]. Combined import
with NGK remains a separate required check.

## Post-first-preflight hardening

The host's --check now independently re-enumerates members and transitive path
dependencies from the staged manifests and compares that closure with the
exported manifest, before cargo metadata. E003 and later run this stricter check.

The final stager also refuses host --check/--extract unless the actual cgroup
limits match 6G/8G/0/64 exactly. Admission still belongs to the unchanged lead
reservation script; this guard does not replace its allowed:true AND exit0 rule.
The owned runner records actual invocation HEAD/dirty state separately from the
configuration's inherited revision label (earlier receipts pin exact source
snapshots and frozen Git revision, but their inherited label can predate launch).
