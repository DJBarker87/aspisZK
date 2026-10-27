# Corrected association kit re-check

Status: BLOCKED / PARTIAL; target not yet established. No premise removed, added or changed. S2 and the 100-bit
release target remain open. Headline: `AspisR1.RPx_Deployed.deployed`.

Binding basis: C3-BIN 2026-10-27 23:00 UTC kit-method ruling and KSA inventory.
A2 is kit-relative only until a successful raw-body re-check; no emission
association is inferred from the old theorem names or receipts.

## Stage 0: scope and inputs

Only KSB-prefixed modules and this evidence directory are writable.
Budget: 150 Lean, 0 Kani, 0 Rust. One capped scope at a time; Lean -M7000,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
Use unchanged S2W runners and coherent SInt2 objects; pin actual Aeneas objects.
Keep `/home/dombarker/project-offloads/codex-cx-kit2-cache-20261027` permanently.

Raw Funs SHA256:
`f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`.
The supplied raw file is not closed over shipped callees. Examples:
`aspis_core.field.QM31.from_le_bytes`, `aspis_core.field.M31.inv`,
`verifier.prepared_claim`, and the circle fallback closure call_once.
These are not Rust std/core library externals. Their absence is distinct
from the iterator/FnMut/from_fn signature mismatch. No replacement is admitted
merely because its name was used in the previous kit.

No shipped source, cfg(kani) harness, other worktree, candidate, wallet or key
changed. No ELF rebuild is triggered. Default/devnet/Pool hashes are inherited,
not newly reproduced. frozen3, RuntimePersistence, ARX_Root, narrowed D188,
security game, failure event, trust inventory and release pins are unchanged.

## Stage 1: exact raw restoration and elaboration obstruction

`KSB_generate.py` reconstructs `KSB_Kit_Funs` from the frozen raw file.
Reversing ONLY the import substitutions and enclosing namespace/section
wrappers recovers every byte of the raw file. `KSB_identity.json` records
all 307 raw declaration spans and identifies all 15 restored edited names.
No shipped-function stand-in is in the new candidate. Types are likewise
byte-exact after import/wrapper reversal; external carriers are explicitly
separate. Library models currently carry no new fidelity credit.

L001 external carriers, L002 raw Types and L003 std/core-only library prefix
pass. L004 WHOLE raw Funs fails: missing shipped callees in addition to the
known iterator ABI mismatch. In particular `QM31.from_le_bytes` is referenced
at raw lines 496/541 and has no declaration in raw Funs; `M31.mul` and
`WideExact.from_limbs` are also missing. The 100-error compiler limit stops
before later missing functions, not a timeout or memory kill. Compiler-generated
sorry diagnostics are rejected; no failed object is accepted as a proof.

The raw translation's dependency boundary is therefore not satisfied by
"raw Funs + Types + std/core externals only". Changing library signatures
cannot define shipped field arithmetic or parser/claim functions. Completing
KIT2 requires additional pinned emitted shipped bodies plus proved carrier/name
associations, or an explicit permitted dependency boundary. No hand-written
shipped stand-in, opaque constant or new premise was introduced to conceal
this obstruction. The whole-kit elaboration item stops here under the
actual-definitions rule; independent kernel-dependency inspection continues.

## Stage 2: merged-theorem dependency re-check

Three fresh accepted kernel inspections: L005 (`XSf_Audit`, A2 first),
L006 (`XSe_FinalAudit`, A6-A8), L007 (`XSd_FinalAudit` and inverse/A1 audits).
They inspect statement AND proof constants, including private/generated
intermediates. They import the old retained environments to diagnose the old
claims; they are NOT re-elaborations against KIT2. L005 prints
`XSf_Closed.prepare` with exactly `[propext, Classical.choice, Quot.sound]`
and its fully explicit existing statement. No new top theorem is asserted.

**A2 NEEDS-REPROOF**, exact kernel path:

```
XSf_Closed.prepare
  → XSf_Closed.narrowed
  → verifier.candidate.wide_view
```

The final definition is the removed shipped stand-in at
`evidence/extraction-assoc6-20261027/XRn_Join_DecodeModels.lean:61`.
A second exact path passes through `XRy_NarrowPrepare.prepare` to the removed
`verifier.prepared_claim` at `XRn_Join_DotModel.lean:75`.
`KSB_A2_dependencies.json` records 17 distinct removed/edited definitions
reachable from this root, with a path for each, and the recorded constant
closure. This is not a complete all-owner KIT2 dependency list. The premise
of job item (3) is false: A2 is NOT restated CLOSED against KIT2.

Selected A6-A8 roots also NEED-REPROOF (all exact paths and source locations
are in `KSB_selected_roots.json`):

- `XSe_HybridCanonical.source` and `XSe_HybridSaved.source` reach the edited
  emitted `XRn_Join_Release.verifier.BatchedWeights.finish`.
- `XSe_NewPhaseSource.source` reaches removed `aspis_core.r0.heap.filled`.
- `XSe_QueryBasis.source` reaches removed `aspis_core.field.M31.ONE`.
- `XSe_ValidatorTransport.source` / `XSe_RecordTransport.source` directly use
  removed `r1_wire.validate_record_fields`; `XSe_ParseFinish.driver` reaches
  it through the actual parse-record constants.

`KSB_theorem_receipts.jsonl` has one receipt for each of 1,099 XR*/XS* source
theorem spans, including diagnostics/WIP as an explicit over-approximation.
343 have exact NEEDS-REPROOF paths to removed stand-ins or edited bodies.
756 remain BLOCKED/unclassified: 357 have no such path in the inspected
prefix graphs, 399 lack an inspected accepted current constant. Absence of a
path is not transfer evidence; no theorem is labelled TRANSFERS or OBSOLETE.
This is explicitly an INCOMPLETE requested three-way triage, not a claim that
all merged associations were checked. Original mathematical/diagnostic kit
statements remain valid within their old scopes. No import-only match is
promoted to a kernel-use path, and no old proof is labelled refuted merely
because a statement mentions an edited definition.

Missing legacy private objects prevent simply importing all older diagnostic
roots; no unchanged cache was rebuilt to infer a transfer while the kit itself
fails. The exact next deliverable is a permitted emitted dependency closure
for the missing shipped callees, then library ABI/fidelity completion and
unchanged proof re-elaboration. The remaining source spans then need actual
per-theorem transfer or precise reproof/obsolescence decisions.

## Validation, provenance and remaining work

Used **8/150 Lean attempts: 7 pass, 1 rejected; 0 Kani, 0 Rust**.
No timeout, memory kill, cap increase, admission refusal, transport retry,
unchanged compiler rerun or full-manifest replay occurred. The single failure
is the intended raw-kit dependency diagnostic. `KSB_VERIFICATION.json` has
zero evidence-consistency errors; that is NOT a successful KIT2 result.
Compiler wall total54.135490339s; maximum peak RSS5,319,328KiB; swap0.
Every exact target/command/revision/source hash/dependency fingerprint/exit/
wall/RSS/swap/axiom print is in `KSB_attempts.jsonl` and per-attempt receipts.

| Attempt | Target | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| KSB_L001 | KSB_Kit_TypesExternal | 0 | 2.624145416 | 2631892 | 0 |
| KSB_L002 | KSB_Kit_Types | 0 | 6.493918561 | 2714348 | 0 |
| KSB_L003 | KSB_Kit_Library | 0 | 3.333678040 | 2664912 | 0 |
| KSB_L004 | KSB_Kit_Funs | 1 | 11.131283607 | 2724896 | 0 |
| KSB_L005 | KSB_DependenciesA2 | 0 | 9.135911032 | 5314356 | 0 |
| KSB_L006 | KSB_DependenciesA6 | 0 | 9.982318423 | 5287776 | 0 |
| KSB_L007 | KSB_DependenciesA4 | 0 | 6.729266110 | 5319328 | 0 |
| KSB_L008 | KSB_AxiomsA6 | 0 | 4.704969150 | 5202720 | 0 |

L008 additionally audits all seven selected A6-A8 roots; every print is
`[propext, Classical.choice, Quot.sound]`. These are existing roots in their
old environments. There are no new theorem declarations or axioms.

`KSB_kernel_object_pins.json` contains read-only POST-audit pins (not invented
pre-launch evidence). All814 inspected module-object selections match the
retained A2/A4/A6 cache manifests, including inherited entries resolved via
their unchanged predecessor manifests. All505 inspected source modules have
exact matching accepted source receipts, and every available A2 source pin
matches the current source. `KSB_provenance.json` records these checks.
Actual Aeneas .olean selections were pinned BEFORE every submission; terminal
checks match all those hashes. Library split objects/IR are also recorded at
terminal time, without pretending that those extra pins preceded submission.

`KSB_terminal_state.json`: all eight owned scopes are gone; no failed Funs
object exists; both runners are byte-identical to the coherent SInt2 runners;
the persistent KIT2 cache and private valid objects are retained. No historical
cache was overwritten or deleted. No binary/object/ELF is committed.

No security assumption, game, metric, failure event, trust boundary, source
adoption or headline premise is discharged/added/changed (0/0/0).
No local association is promoted to a complete source, native or release proof.
A2 remains closed relative to the old kit only; A6-A8 remain open. Other rows
receive no fresh closure credit. The original 100-bit release target remains
not established. Inherited, NOT rebuilt, ELF SHA256 pins:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Completion requires additional pinned emitted implementations of the missing
shipped dependencies, with appropriate proved carrier/name adapters and the
CLOSED leaves' actual domains; only then repair the library ABI and complete
its separately assigned fidelity obligations, elaborate the whole kit, and
re-elaborate the unclassified proofs. No substitution of a new opaque premise
or hand-written shipped implementation is proposed. The pending clarification
asks whether that additional emitted dependency closure is within KIT2 scope.
No further compiler launch is useful under the current raw-only boundary.
All stage commits are local; no push or merge.
