# NCX current registry decoder handoff

**Partial native result. The requested current-format model observations are
proved; full op33/op34 native P6 bridges remain OPEN. S2 / the deployed 100-bit
target are not established.** Branch: codex/cx-native-decref2-20261028. No push.

## Ready for JHu

Import `NCX_JHuObservations`. Its `registry base` and `entry base` prove exactly:

```lean
(JHd_ReferenceSlots.install (NCV_Install.install (NCX_Install.install base))).op33
  JHb_DataRegistry.value = ok (.Ok JHj_RegistryValue.registry)
(JHd_ReferenceSlots.install (NCV_Install.install (NCX_Install.install base))).op34
  JHb_DataEntry.value = ok (.Ok JHj_RegistryValue.entry)
```

These are complete evaluations of the actual extracted reference bodies, not
registry-success hypotheses or selected successful callbacks. Every field and
all format/validation gates are evaluated through symbolic field/scan lemmas.
Registry bump255 and ProgramData bump255 are retained; entry bumps are254.
The August V7 extraction is excluded. `commute` proves that NCX/NCV installation
order agrees; `runtime_retained` preserves op38 and coherent digest/error slots
op43/op44; `ncv_retained` preserves op48/op49/op50.

`NCX_reference.rs` is the complete safe Rust reference, derived from frozen
current source4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. `NCX_SOURCE_PINS.json`
records transformations. `lean/NCX_Reference/{Types,Funs}.lean` is the exact E002
output. The NCV Charon/Aeneas binary pins and nightly-2026-09-17 are retained in
NCX_EXTRACTION_PINS.json; no external template was emitted. E001's missing
Option-item error is excluded; E002 adds NCV's explicit language-item helper.

`NCX_Carrier` gives two-sided record/status/error conversions, retaining all
12 error variants. `NCX_Install` installs op33/op34 and preserves outer
fail/div. `NCX_Configuration` separately exports `NCX_Install.configure missing`,
which updates missing.adapter alongside NCV, plus exact SDK selections.
Configuration and fixture stacks have separate audits: broad configuration
support plus the fixture imports encountered an existing duplicate owner
(S2K_LateAdmission / JHb_S2K_LateAdmission) at L026. Factoring our dictionary
from our configuration module fixes the requested fixture imports without
editing any existing owner. No joint SDK configuration/fixture root or native
AeneasExtraction instance is claimed.

## Native evidence

All40 runs select exact harness names, use deployed features and frozen lock,
validate the resolved graph before launch, run offline and check unchanged lock
afterwards. Each graph receipt records every crate's features. Exact KMX patch:
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.

- K001/002:32-byte KMX copy pass/failing control.
- K004/005 and K006/007: actual registry/entry validator contracts against
  safe natural byte specifications, every complete typed record, exact errors.
- K014/015: actual registry decoder/reference equality on the documented
  five-way rejection split; not all lengths or accepted inputs.
- K027/028 and K029/030: native range/cast and LE word windows, arbitrary
  relative offset and byte; exact64/16-byte backing domains are local fragments.
- K034/035: actual status conversion versus reference, every u8.
- K036/037: actual private zero-binding helper versus reference, every32 bytes.
- K038/039: actual entry decoder/reference equality at empty length0 only.
- K008–012, K017–021, K022–026: contract fidelity controls for the registry,
  entry and Result<Unit,FormatError> shapes respectively. Positive contract and
  real-body assertions pass; inverted ensures, unlisted modifies and unimplied
  stub_verified caller assertions fail. No slice/Vec/Box return substitution.
- K040: deliberately weakening the cast window bound from p≤32 to p≤33
  exposes the native slice panic. Negative domain control, not a shipped bug.

K003/K013/K016/K031/K032/K033 TIME OUT and receive no credit. This includes both
scalar-coordinate native callers under verified validator contracts. No timeout
was raised or replayed unchanged. No field multiplication, SHA syscall, custom
copy stub or Option<fn>-dependent evidence is used. The only actual callee
stub_verified experiments are K032/K033, both excluded caller timeouts; their
callee contracts and matching controls passed. Field arithmetic stubs: none.

## Remaining, member by member

| Member | Established | Exact remaining native obligation |
|---|---|---|
| op33 registry | Current extracted body, lossless conversion, dictionary/SDK selections, complete fixture observation; validator and cast/word/zero local checks; selected rejection class. | Original native range/cast/record pre-state association, complete Result equality on accepted inputs and remaining rejection lengths/classes, and the actual SDK op33 call association on the same input. |
| op34 entry | Same model/fixture delivery; validator/status/zero/window checks; native empty-length rejection. | Original native status/range/cast/record association, full accepted/error Result equality beyond empty input, and actual SDK op34 same-input association. The combined and magic-only rejection shapes timed out. |

Next concrete deliverable: a native one-field cut from the ORIGINAL decoder
pre-state, identifying its actual32-byte slice with the checked cast window,
then the same-record validator and returned-record/error construction join.
Consume the existing local checks and symbolic ParsedBodies/ResultObservations
laws; do not replay the six retired timeout shapes or increase caps.

NCX_ParsedBodies assembles each parser from its individual observations with
arbitrary validation outcome; no validation success is assumed.
NCX_Observations/ResultObservations prove full record/Result extensionality.
NCX_WindowFrames proves reference locality and exact KMX disjointness/outside
value laws. NCX_CallerDomains proves every real format offset and scan bound
from the format-length guard. These do not prove native pointer/caller
association. No64/16 backing bound is imposed on the real256/320-byte caller;
transport from local windows remains an explicit native obligation.

Budget: **40/40 Kani,42/60 Lean**, plus2 separately capped extractions. Native
exhaustion was followed by the remaining Lean composition/domain/fixture/audit
work. No requested independent Lean-only member remains: both model bodies,
conversions, installation selections, fixture observations, loop reuse, locality,
frames, bounds, status and Result composition are checked. Each still-open row
in the table requires new native/P6 evidence; restating it as a Lean hypothesis
would not discharge it. No further Kani launch is authorized. Other units and
the full seventh authentication-child/SDK/headline composition are outside this
decoder lane, not silently declared closed.

## Audits, receipts and retention

26 canonical modules match exact-source passing receipts. L041 audits118 new
statements plus9 extracted definitions: exit0, wall2.050638081s,
peakRSS5,444,584KiB, swap0. L042 audits the2 configuration statements: exit0,
wall2.663514576s, peakRSS5,576,280KiB, swap0. Source revision for both:
fdf08104cf plus the exact dirty source hashes recorded in their receipts.
All120 new statements use only propext/Classical.choice/Quot.sound or a subset.
42 Lean attempts:31 pass,11 excluded elaboration/import drafts; total85.125125s,
maximum5,640,852KiB.40 Kani attempts:15 pass,19 intended failures,6 timeouts;
maximum6,475,456KiB. All swaps0. Every scope:6G high /8G max /swap0 /64 tasks;
Lean -M7000; optimized Rust; allowed:true AND admission exit0; one scope at once.
No admission/transport retry, memory kill, cap increase or cold dependency build.

NCX_ATTEMPTS.jsonl contains exact commands, targets, revisions, source and
selected dependency hashes, exit/wall/RSS/swap/limits and full axiom lines;
raw logs and source snapshots accompany it. Native harnesses are patch-only.
NCX_VALIDATION.json verifies all source hashes, deployed feature/graph/lock
receipts, axioms and reconstruction of ALL40 native patches from frozen source.
The converter accidentally emptied K004–015 patches when it visited already
empty snapshot directories. NCX_PATCH_RECOVERY.json records their recovery
from immutable host snapshots and exact source-hash verification; no proof was
rerun and no receipt was changed. Generator outputs reproduce byte-identically.

NCX_POSTFLIGHT.json verifies498 frozen source/root files:495 unchanged scratch
files, and3 exact cfg(kani)-only parent overlays that strip to frozen bytes.
The repository's shipped files remain byte-identical. All692 imported cache
files and219 actually resolved Aeneas objects are unchanged.26 canonical NCX
objects are retained in /home/dombarker/project-offloads/codex-cx-decref-cache-20261028.
Own675,727,533-byte Rust target,412,808-byte extraction target and compiled
scratch were removed after retention checks; the cache is retained. No key or
wallet operation, existing-module/worktree/candidate edit, push or merge occurred.

This is focused evidence on the pinned coherent selection, not a new full
frozen-manifest or ELF replay. No shipped-file rebuild trigger occurred.
Inherited, not newly reproduced ELF pins:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Headline remains AspisR1.RPx_Deployed.deployed. Frozen3, L154, narrowed D188,
RuntimePersistence, game, metric, numerical bound and existing runtime/SDK/std/
allocator/ABI/source-to-ELF obligations are unchanged. No trust item or
cryptographic premise is added or discharged; no XRn join kit is used.
