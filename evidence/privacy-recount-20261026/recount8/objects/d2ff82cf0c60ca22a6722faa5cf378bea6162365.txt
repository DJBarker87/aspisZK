# D390 in-progress state

Worktree and branch unchanged; entry bda15710cf. Ruling x-prime supersedes
only extraction's toolchain requirement. Kani remains prohibited in this run.
IDs 42000–42099 remain the sole block, audits 42097–42099 reserved.

The E0514 blocker is resolved by the permitted pinned nightly extraction.
The original byte-identical copy's 64-case rustc1.94.1 release differential
is reused as finite validation. New owned reference changes require their own
native validation and structural laws; no closure is credited from them yet.

Seven Lean attempts launched: 42000 selection-model facts PASS; 42001 deployed
conversion emission PASS; 42002 conversion laws FAIL (two usize bounds);
42003 corrected conversion laws PASS; 42004 selection emission PASS;
42005 indexing law FAIL (length-vs-size premise); 42006 corrected indexing PASS.
No audit IDs used, no Kani launched. Full receipts await archive collection.

The library capture for the current direct 25 LLBC declarations identifies
21 identical source bodies and four differing conversion bodies. The four
1.94.1 expressions are independently extracted and their complete Result /
value laws pass. This direct-declaration inventory is NOT yet a complete
transitive standard-library audit.

The `absorb` extraction emits about 5,000 lines of concrete Lean but retains
external templates for projected Poseidon, integer intrinsics, Option equality
and constants. It is raw evidence, NOT an accepted complete extraction. The
`masks` extraction eliminates the intrinsics and Option template using a
seven-mask specialization and explicit checked-add matching; it still has the
Poseidon evaluator and one depth constant. No template axiom is compiled.

Owned proof-only sources now contain a projected Poseidon copy, fixed3/fixed7
field helpers, fixed-size closure/iterator removal and ordered loop unrolling.
All of those differences need their structural proof and native check. The
full projected-loop extraction is currently running with timeout300 and the
unchanged 6G/8G/swap0/Tasks64 caps. The next Lean sources are SelectStep227,
SelectLoop227 and Mask227. Native changed-reference finite227-owned is prepared
but has NOT run. At most one capped scope runs at a time.

V244 OPEN; V241/V245 untouched under the finish-V244-first instruction.
V228/V229/V243 retain accepted closure status. No row/endpoint premise removed,
added, weakened or moved into T; T remains entropy_law/entropy_kernel/observation.
Target not yet established. No row/endpoint counterexample found.


## Additional checkpoint (before retry 42056)

56 charged Lean attempts, 0 Kani. The final 42056 admission was refused (78, allowed:false) at 20:09:12 UTC, retry no earlier than 20:12:12 UTC with the same ID. Complete extraction and 64-case changed-reference native validation passed. Complete emission compiles through chunk19; chunk20 prepared3 is under elaboration repair. Type/pure-bind/array sharing transformations retain raw emission and explicit roundtrip records. V244 remains OPEN; no original-carrier installation or whole source binding/nonvacuity is claimed. Native/emission mutable-write checks are prepared, not run. Standard source expanded inventory is53 declarations;40 bodies identical,4 conversions have separate laws, additional slice model law passes but actual caller/index correspondence remains open; compiler glue/intrinsic boundaries explicit. V241/V245 untouched under row-first order.


## Checkpoint after 42087

88 charged Lean attempts, next42088; 42097-99 still reserved. Exactbranch/worktree unchanged. All P227_00..12 compile (P03 has four isolated03a..d plus aggregator). P13 old composition was stopped143 at RSS8885688KiB, loop-only P13a passes42087. Owned Rust now factors3fixed16 claim selections into select_c1_227; new720-filefreeze native227-composition-source-freeze.json. Native64 newcomposition passes (native227-resume5-owned-composition), Charoncomposition passed after180s refusal cooldown; Aeneascomposition currently running via SSH session67852 (do not duplicate). Fresh raw output must go raw227-composition-resume5; tools/port_composition227_resume5.py prepared to validate onlycompositionchanged+1newselect helper, reuseallotherbody-identicaldefs, produceP13b andredirectP14import. Needcommit/authority/upload/compileP13b thenP14. Then RootLaw227,RootD227, originalcarrierBytesV3Types226/Carrier227/Install227 andpossiblyclosedrootinstance; only9 nonaudit compile slots remain, so prioritizewholeResult/source andcarrier. Budgetstop100 mandatory. No rowclosureclaimed; FormalOk-nonvacuity/universalstructuralbinding andsomeD188/directwrites andpreinlineStdcone remain.

Native/emission36 helperobservations matchPASS42079 (first42078 hadonlylayoutparseerrorsfor8cases, retained). Comparison=fidelity227-comparison-resume5.json; native+Leanobservationfilesretained. Three-restoration-function evidence includesprepared3caller, notdirectintermediatearraystate foraccumulate helper; do not overcreditper-functionD188. Freshpartsstd53 declarations sourcecompared,5different (4conversionlawspass; slice-model+boundassociationnotcomplete); 13additionalinlineduintmacrobodycomparisonsidentical. CompletepreinlineStdreachabilitynotclaimed. Newsourcecompositionstdinventorynotyetcaptured; oldstdsourcefiles/toolchaincohortunchanged.

Two manualnativePV_REV labeltypos were correctedagainst720-filefreezeswithoriginalreceipts/featurespreserved. Firstnativeparts andfidelitynative nowcorrectf5e94cd833f5fd669f684212186e771debf7128a. Scripts nowreadrevisionfile directly; nevertranscribefullrevisionhash. Nativecomposition readsH/revision; actualsourcepin isrust-composition-revision.txt fromgitrevparse. Sourcehashesalwaysmatched.

CurrentnewproofRootLaw227 isuncompiled draft: actualcomposition/equalityclosedemittedbodiesretainedintheplan; doesnotprovethosebodynativecorrespondence orOk-nonvacuity. RootDuncompiledgenericwholeemissionDindependence. Carrier227 uncompiled hasbijectiveQ/array/challengeconversions andsemanticprojectionintoSource, Typesop6/op20new227, op21/22accepted226pubrecords. Install227genericterminalargumentstilluncompiled; all261otherfieldsframed. Freshh5closure3Fullmodulescompiled42060/61/62, AeneasRootdirecth4preflightpasses. BytesV3Types226notyetcompiledinnewcache. Sourceauthoritymanifestupdatedasmodulescommitted; mustregisternextnewmodulesbeforehostcompile. No oldprivatecarrierobjectsremain; no otherjobobjectsused.

Finalevidence/staleFINAL.md stillmustupdatebeforeend. Archivecollectorneedsrefreshafterworkends; currentlysupportsallnativeprefixesandfidelity. Allreceipts throughold16locallyarchived; new88hostreceiptsnotyetcollected. Preservefailedcandidates; compressanyindividual>20MBwithSHA. No keys/wallets, no crates/programs, no sharedhostsources modified. No Kani, no subagents, no push/merge. Targetnotestablished. T unchanged3items.


## Final checkpoint — 100/100 attempts

All IDs42000–42099 are charged; zero Kani runs and zero Lean attempts remain.
Combined installed-Result bridge42097, standard-axioms audit42098 and supporting
replay42099 passed. RootLaw227 and the concrete op227 installation with261
other-field frames are checked. RootD227's theorem compiled inside the combined
module; the standalone RootD file remains an uncompiled draft.

Final extraction, deployed1.94.1 native64 validation and36 arithmetic
native/emission observations pass. V244 remains OPEN: universal shipped-source
binding, formal successful nonvacuity, remaining write checks and full std-cone
application are outstanding. V241/V245 were not started under the required order.
Accepted V228/V229/V243, T and endpoint premises remain unchanged.

All177 receipts and compressed LLBC snapshots are archived locally. Final source
revisions, resource measurements, corrections, failures and residuals are recorded
in FINAL.md, RECEIPT-NOTES-resume5.md and RESIDUALS-resume5.md. Own rebuildable
host caches were removed after recording their hashes; sources and evidence were
retained, with no keys deleted. No more compilation or extraction is authorized
by this exhausted budget. This checkpoint supersedes the earlier pending-work
notes; the final stop reason is budget exhaustion, not E0514.
