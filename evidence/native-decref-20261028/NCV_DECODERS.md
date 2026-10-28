# NCV decoder bodies

Status: work in progress; op48, op49, op50 OPEN. No security closure claimed.
Frozen Rust: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Headline: AspisR1.RPx_Deployed.deployed. No source adoption or trust change.

| Slot | Reference | Extraction | Native equality/control | Installation | Fixture |
|---|---|---|---|---|---|
|48 master|NCV_reference.rs|E008; L002/L003 PASS|pending|pending|pending|
|49 checkpoint|NCV_reference.rs|E008; L002/L003 PASS|pending|pending|pending|
|50 lane|NCV_reference.rs|E008; L002/L003 PASS|pending|pending|pending|

Budget: 60 Lean / 60 Kani under the job-specific final allocation. One scope at a time.
Only NCV modules and this evidence directory may change. Scratch source is outside
this repository; all harness changes will be retained as patches. Existing proved
modules, session A worktrees, shipped files and frozen lock are read-only.

## Stage 1: complete reference extraction

NCV_reference.rs contains safe reference bodies for all three wrappers. Helper
errors collapse to Unit because every wrapper maps them to InvalidAccountData;
the Aeneas Result layer remains distinct. The reference uses explicit byte reads,
checked canonical limbs, full master policy/state validation and all twenty lane
frontier conditions. EMPTY is copied from the frozen verifier table (168 limbs).

NCV_E008 extracts all three bodies using the NCO pinned Charon/Aeneas hashes and
nightly-2026-09-17; exact commands, source hash and output hashes are in
NCV_EXTRACTION_PINS.json. No FunsExternal template was emitted. NCV_L002 and
NCV_L003 compile Types/Funs in Lean 4.32.0 against the pinned SInt2 library.
There are no added top theorems in these generated files; axiom audit is pending
for the installation/proof modules. This is reference extraction, not native
refinement or a cohort installation.

Failed experiments are retained: E001/E003/E006/E007 hit the pinned Aeneas
loop-context Not_found exception. E004 identified the separate missing Option
language-item requirement; E005 passes after making that language item reachable.
E008 moves sequence/frontier loops into separate reference helpers, avoiding the
loop-context exception without modifying tools. L001 typechecked but could not
write its output because this job omitted the nested output directory; L002
corrects the own-runner input directory. No timeout or memory kill was rerun.
