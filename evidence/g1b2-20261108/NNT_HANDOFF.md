# NNT relational G1b handoff

Status: all L1-L11 delivered and audited; no release claim. Branch
codex/cx-g1b2-20261107. Only NNT_ files in evidence/g1b2-20261108 are changed.

## Delivered mathematical statements

The literal implementation is NMX_R9_StageTwo.stage2 ch, with unchanged
RowSpecs, Dom064, deployed IDs and canonical library. RSL.NNT.LawRefines is
exactly G1BP sections 1 and 4. RSL.NNT.NMS_RootsL and NNC_G1aL retain the
unchanged r242, writeFree and okHeader types; projection rfl checks are in
NNT_Interfaces.lean. No statement about LawRefines at wEnv is made.

L1 NNT_Verify241.verify_law; L2 NNT_Port241.root; L3
NNT_RelReplay241.relPacket_iff/fold; L4 NNT_Native241.full; L5
NNT_Root241.parametric/weak_instance/canonical_instance; L6 NNT_Field.r241;
L7 NNT_LawOk.native_of_ok; L8 NNT_G1aLaw.native_bytes_of_ok/okHeader;
L9 NNT_G1aLaw.field; L10 NNT_WeakEntryLaw.produce.

L6 is at NNS_Field.install I0 ch (reused read-only): f241 is the literal
credited stage2, f242 is validate ch. NNT_Field's Required proposition and
its installed NMS_RootsL projection are definitionally identical. The canonical
row type is definitionally identical to NMX_R9_StageTwo.root's conclusion;
the original credited root is unchanged. L9 uses w := V0.tx2auth and imposes
no f064 instance. It works for every I and uses NNH_G1aEnv.sig S solely to
install the same concrete readerHeader definition as the merged G1a field.

## Full consumer restatements

NNT_TopLCore/Event/B/TopL split elaboration into four serial modules; they
share namespace NNT_TopL. NNT_STATEMENTS.md records full before/after
statements for all 18 restated theorems, including entryRoot, weakEntry,
canonicalRef240, asq8Frame, top, event_top_splitB/full, top_splitB,
fail_sub_rec, deployed_charge, top_splitB_counts/physical and selected_top_split.
NNT_STATEMENT_CHECK.json mechanically checks the statements differ only by
NMS_RootsL, NNC_G1aL, entryRoot's LawRefines and unused nmn removal.
NMFPrime/CaseSplit/NMFPrimeB have their complete original field statements
re-expressed over the new G1a carrier; all remaining structures are reused.
The physical final target is NNT_TopL.top_splitB_physical.

## Validation and export

Final receipts, exact object export and hashes are recorded below. NNT_COMPILE.tsv records each exact target, exit, wall, peak RSS,
swap, source revision/hash, dependency receipt and printed axiom lines.
Raw ax2 uses ledger29's unchanged optimized walker by reference, with its
unchanged fixtures. NNT_PIN_CONSISTENCY.json checks selected NNH/Aeneas
hashes across launches; full selected closure pins are retained separately.
No cache copying, moving or deletion. No push, Kani, extraction, Rust, SBF,
shipped-file change, key or fund action. ELF rebuild trigger did not fire.

Ruling (bu)'s owner-visible caveats and the remaining G0 work are explicit
in NNT_REMAINING.md. The work establishes top-composition fields, not the
100-bit headline. Inherited frozen ELF pins (not rebuilt): default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc.

target not yet established

## Exact interface delta (before/after)

The original r241 field is:
```lean
∀ R0 w, TAS.Refines064 V0 I.f064 R0 w →
 TX2_242.RowSpec_242 L D I.f242 →
 TX2_241.RowSpec_241 L D (TAS.lib V0 R0 w) I.f241
```
The delivered r241 field is:
```lean
∀ R0 w, RSL.NNT.LawRefines V0 R0 w →
 TX2_242.RowSpec_242 L D I.f242 →
 TX2_241.RowSpec_241 L D (TAS.lib V0 R0 w) I.f241
```
The original G1a `weak : TAS.Refines064 V0 I.f064 (fun _ _ => True) w`
becomes `lawRefines : RSL.NNT.LawRefines V0 (fun _ _ => True) w`.
The `w`, `writeFree` and `okHeader` field types are unchanged. The delivered
instance sets w to V0.tx2auth; its lawRefines field is reflexivity. This is
the authorised replacement of incomparable premises, not a premise weakening.

NNT_L018/stdout.log contains elaborated types of the delivered constants,
including every consumer. NNT_STATEMENTS.md is the full source-level
before/after table; the comparison checks 18/18 statements.


## Final validation and G0 export

24/30 serial capped scopes used: 18 Lean (17 pass, one retained syntax error),
one fixture scope, four raw-audit scopes and one retention scope. All later
attempts pass. No timeout, memory kill, cap increase or unchanged regression
rerun. Every admission exit0 and allowed:true; whole-host count<6; disk≥40GB;
6G high / 8G max / swap0 / tasks64, Lean v4.32.0 -j1 -M7000 async=false,180s.
Total scoped wall505.057s; maximum RSS7,209,852KiB; all swaps0. L017 combined
import: exit0,27.998s,6,892,836KiB. L018 elaborated types: exit0,27.652s,
6,880,708KiB. L020-L023 raw audits:13/13 standard-only, matching collectAxioms.
All eight unchanged walker fixtures pass, including intentional planted
nonstandard-axiom negative controls (not delivered theorem dependencies).

G0 should prepend:
`/home/dombarker/project-offloads/codex-cx-g1b2-20261108/NNT_objects`
then retain the exact remaining order in NNT_EXPORT.json's LEAN_PATH (NNS_v2,
NNS_primary, the pinned inherited paths and read-only NNH run-5 objects; NNN's
small export is referenced at the end). NNT_EXPORT.json pins all16 own modules
and companions by SHA256. NNT_CLOSURE_PINS.json.xz plus its uncompressed SHA
pins19,323 selected modules /35,919 files, including the resolved Aeneas library
objects and exact NNH objects read. NNT_PIN_CONSISTENCY.json finds zero changes
across645 NNH/Aeneas object/companion pins between attempts. Every NNS export
hash matches its inherited manifest. No cache/export object was copied, moved
or deleted. This is a focused cached composition, not a cold release rebuild.

All assigned members are complete, so the remaining six scope slots are not
spent on unrelated work or duplicate successful regressions. Ledger30 remains
599 CLOSED; this job closes no ledger row. The interface change and retained
A2/off-Root0 caveats above remain visible. Stage commits are listed in
NNT_COMMITS.txt (before this final handoff commit); no push.

target not yet established
