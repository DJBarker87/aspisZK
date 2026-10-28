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
