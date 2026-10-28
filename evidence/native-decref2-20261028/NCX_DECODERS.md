# Current registry decoder ledger

Status: OPEN. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Headline AspisR1.RPx_Deployed.deployed; op33 registry and op34 entry.
Budget 40 Kani, 60 Lean. One admitted capped scope at a time.
No shipped changes; harnesses are scratch-only and delivered as patches.

The August extraction is excluded: current registry byte 7 is the PDA bump,
byte 248 is the ProgramData bump, and reserved bytes start at 249.
Current entry bumps are bytes 312 and 313; reserved bytes start at 314.

Stage 1: NCX_E002 extracts both current references with the NCV tool pins.
NCX_E001 is a rejected missing-Option-item extraction, not proof evidence.
NCX_L001/L002 compile Types/Funs (-M7000; capped host; exact receipts).
No external template was emitted. Safe casts preserve exact width; native
source correspondence and fixture evaluations remain OPEN.

Stage 2: NCX_Carrier roundtrip/surjectivity covers both complete records,
all four statuses and all twelve exact error variants (L003). NCX_Install
selects op33/op34 in missing.adapter and in the SDK, alongside NCV_Install's
op48/op49/op50; preserves outer failure/divergence (L004). These are dictionary
selection results, not a discharged AeneasExtraction/native P6 boundary.
Axioms are standard only; no hypotheses/trust items were added or changed.

Native intermediate results: K001/K002 KMX32 pass/failing control; K003 full
registry decoder timeout; K004/K005 registry validator pass/failing control;
K006/K007 entry validator pass/failing control. K008–012 calibrate the exact
Result<VerifierRegistryV2,FormatError> contract shape: positive contract/real
caller pass, inverted ensures/unlisted modifies/stub caller fail. K013's
arbitrary-coordinate registry wrapper timed out and receives no credit.
K014/K015 original registry decoder equality passes/fails on selected five-way
rejection splits (wrong length257, first magic byte0, version0, mode0, first
reserved byte1). This is not arbitrary malformed-input coverage or success.
No timeout was rerun unchanged or with increased caps. No field arithmetic,
SHA syscall or Option<fn>-dependent result is credited.

Stage 3: both complete extracted fixture observations are proved, with no
registry-success hypothesis. NCX_RegistryFixture.source (L013) and
NCX_EntryFixture.source (L021) use symbolic field/scans; NCX_FixtureCarriers
(L025) identifies every converted field with JHj_RegistryValue's exact records.
NCX_FixtureObservations (L030) exports registry/entry and installed_registry/
installed_entry under JHd_ReferenceSlots.install, alongside NCV_Install.
These are the two model observations needed by JHu_, not native P6 closure.

NCX_Install is deliberately small. NCX_Configuration separately imports
NCV_InstallationSupport to retain SDK selection and NCV slots (L028/L029).
This avoids an own broad-import duplicate-owner collision between the
configuration and fixture stacks (L026); no existing owner was rewritten.
NCX_Observations gives full record extensionality from arbitrary coordinates
(L024). NCX_LengthRejection proves all reference non-format lengths reject
(L023), without a bounded-slice premise.

K016 combined entry rejection split timed out; no credit, no paired replay.
The following smaller native shapes remain independent.

Stage 4: Kani exhausted at 40/40. Totals: 15 local PASS, 19 intended failing
controls/domain probes, 6 TIMEOUT (K003/K013/K016/K031/K032/K033). No whole
native decoder/P6 bridge is claimed. K032/K033 are scalar-coordinate caller
splits under the passing actual validator contracts; both timed out, excluded.
The Result<Unit,FormatError> calibration K022–026 precedes those substitutions.
K017–021 similarly calibrate Result<EntryV2,FormatError>. No slice/Vec/Box
return is used with stub_verified.

K027/028: native 32-byte range/cast vs read32 at arbitrary p≤32 within64 bytes,
arbitrary j<32. K029/030: native eight-byte LE word vs word at p≤8 in16 bytes.
K034/035: native TryFrom<u8> vs status for every u8, exact status/error.
K036/037: actual private required_binding_is_zero vs the safe zero scan on
EVERY32-byte array. K038/039: actual entry decoder/ref equality at empty length0.
K040 deliberately weakens the K027 bound to p≤33: the slice panic is detected.
That negative domain probe is not a shipped decoder bug or an enlarged domain.
Every passing contract has its matched failing control with exact KMX/features.

Native window backing-size domains are LOCAL FRAGMENTS. The actual decoder
buffers are256/320 bytes; no upper bound64/16 is imposed on their callers.
NCX_WindowFrames proves symbolic reference locality, exact KMX disjoint-copy
and outside framing laws for the current field offsets. NCX_CallerDomains
proves every array/word/header/reserved and binding-scan bound from the actual
format-length guard. The remaining native slice/cast/record call association
is OPEN: those value/domain laws do not silently close it.

NCX_ParsedBodies assembles both parsers from explicit field observations,
including the validator's exact success/error/fail/div result; it assumes no
validation success. NCX_StatusSpec covers all status values. NCX_Observations
and NCX_ResultObservations recover full records and exact Result equality from
all valid coordinate observations. These are symbolic model composition laws.
NCX_JHuObservations exports the exact two observations in JHu's NCV-before-NCX
order, proves dictionary commutation, and retains op38/op43/op44 and NCV slots.

Final evidence: NCX_VALIDATION.json verifies26 current modules,120 new theorem
statements,9 extracted definitions and reconstruction of all40 native patches.
L041/L042 audits pass with standard axioms only. K004–015 patch recovery from
immutable host snapshots is recorded in NCX_PATCH_RECOVERY.json; no receipt or
proof was changed. NCX_POSTFLIGHT.json confirms498 source/root pins,219 resolved
Aeneas objects,692 unchanged imported cache files and26 retained own objects.
See NCX_HANDOFF.md for exact remaining rows, budget/stop justification, audited
scope limitations, resource metrics and inherited ELF pins. Target not established.
