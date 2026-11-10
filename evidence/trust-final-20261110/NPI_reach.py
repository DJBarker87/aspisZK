#!/usr/bin/env python3
"""NPI_ A1: reachability of every trust row and reviewed-transcription item from the replayed cones.
Inputs (argv): scratch dir holding ledger.json (xz -dc NNN_LEDGER.json.xz), cone_splitB.txt, cone_charge.txt
(xz -dc of the L187 final REACHABLE lists; sha256 checked against their sidecars), and out/run/NPI_out_*.tsv
(the NPI_L004 census). Writes NPI_TRUST_REACH.json next to this script."""
import json, sys, hashlib, collections, os
S = sys.argv[1]; HERE = os.path.dirname(os.path.abspath(__file__))
sha = lambda p: hashlib.sha256(open(p,'rb').read()).hexdigest()
PIN = {'cone_splitB.txt':'0b316cbba462874e984430db4c9ddcaa2d902053315934a8b608eaea48d30090',
       'cone_charge.txt':'4ae9686fc22d0b46497f02c1730f121ff5045147dc3ef895f2fac188455d6a58'}
for f,h in PIN.items(): assert sha(f'{S}/{f}') == h, f
d = json.load(open(f'{S}/ledger.json'))
cs = set(open(f'{S}/cone_splitB.txt').read().split()); cc = set(open(f'{S}/cone_charge.txt').read().split())
def nm(n, c):
    if not n: return None
    for x in (n, 'AspisR1.' + n):
        if x in c: return x
    return None
# Rows whose ledger root is restated at the top (NNH_Run6Fields / NVR_* / NNT_Field, TAS_G0_AUDIT field_installations):
INSTALLED = {
 'TX1:330': ['NVR_Folds.process_tx1', 'RSL.TX1_330.RowSpec_330'],
 'TX1:333': ['NVR_Folds.process_tx1', 'RSL.TX1_333.RowSpec_333'],
 'TX2:213': ['NVR_TAS.r213', 'NVR_Folds.entry_tx2'],
 'TX2:221': ['NVR_TAS.r221', 'NVR_Folds.process_tx2'],
 'TX1:344': ['NVR_TasRoots.field344', 'NMV_ConcreteWindows.root344'],
 'TX2:240': ['NVR_TasRoots.field240', 'NMV_ConcreteWindows.root240'],
 'TX2:241': ['NNT_Field.r241', 'NMX_R9_StageTwo.stage2'],
}
rows = {r['row']: r for r in d['rows']}
def row_reach(rid):
    r = rows.get(rid)
    if r is None: return dict(row=rid, in_ledger=False, reached=False)
    roots = [x['root'] for x in r['root_owners']]
    rs = [x for x in roots if nm(x, cs)]; rc = [x for x in roots if nm(x, cc)]
    inst = [x for x in INSTALLED.get(rid, []) if x in cs and x in cc]
    return dict(row=rid, function=r['function'], roots=roots, roots_in_splitB=rs, roots_in_charge=rc,
                installed_field_constants=inst, reached=bool(rs or rc or inst))
allrows = {k: row_reach(k) for k in rows}
cnt = collections.Counter('NO_ROOT_RECORDED' if not v['roots'] else 'ROOT_IN_CONE' if (v['roots_in_splitB'] or v['roots_in_charge']) else
                          'INSTALLED_FIELD' if v['installed_field_constants'] else 'NOT_IN_CONE' for v in allrows.values())
def consumers(t):
    return sorted(set(t.get('direct_closed_rows', [])) | set(t.get('consumed_by_closed_rows', [])))
def summarize(rids):
    rr = [allrows.get(x) or row_reach(x) for x in rids]
    return dict(n=len(rr), reached=[x['row'] for x in rr if x.get('reached')],
                not_reached=[x['row'] for x in rr if not x.get('reached')])
consumes = collections.defaultdict(list)
for r in d['rows']:
    for x in r.get('consumes_trust') or []: consumes[x].append(r['row'])
cen = {}
for l in open(f'{S}/out/run/NPI_out_targets.tsv'):
    p = l.rstrip('\n').split('\t')
    if len(p) >= 3: cen[p[0]] = dict(exists=p[1] == 'true', in_cone=p[2] == 'true', module=p[3] if len(p) > 3 else None)
def cone(*names): return [n for n in names if n in cs and n in cc]
ledger_trust = {t['id']: t for t in d['trust_rows']}
def L(i):
    t = ledger_trust[i]; c = consumers(t)
    s = summarize(c); s2 = summarize(consumes.get(i, []))
    return dict(ledger_status=t.get('status'), ledger_consumers=s, ledger_consumes_trust_rows=s2)
R = []
def add(row, cls, enters, reached, constants, note, ledger_id=None, owner=None):
    e = dict(row=row, class_=cls, enters=enters, reached=reached, lean_constants_in_both_cones=constants, note=note)
    if ledger_id: e['ledger'] = L(ledger_id)
    if owner: e['added_under_delegation'] = owner
    R.append(e)
add('Random-oracle model for SHA-256 (L194)', 'oracle model', 'statement (H universal; every probability over H)', 'YES',
    cone('AspisR1.F3T_RuntimeBound.failureModel','AspisV8R19.MemoizedProgramLaw.lazyMean'), 'Not a Lean premise; the reading of H.')
add('P1 ideal-oracle realization', 'oracle model', 'INSTANTIATED (sha256 := H, p1 := rfl, ruling (bt)); row is the physical reading', 'YES',
    cone('AspisR1.S2W_ExtractionBoundary.P1.mk','AspisR1.S2W_ExtractionBoundary.P1.realization'), 'Lean premise discharged at the top; P1.mk built inside the cone.')
add('RuntimeSyscall.returningValue', 'runtime', 'INSTANTIATED (DGP_HostDigest.syscall theorem at hashAdapter H); row is the physical reading of every returned digest in Runs', 'YES',
    cone('AspisR1.S2W_ExtractionBoundary.RuntimeSyscall','AspisR1.S2W_ExtractionBoundary.RuntimeSyscall.mk','AspisR1.S2W_ExtractionBoundary.RuntimeSyscall.returningValue','AspisR1.DGP_HostDigest.syscall','AspisR1.S2Z.Oracle.RuntimeSyscall'), '')
add('RuntimeSha256Value', 'runtime', 'META: physical reading of the SolanaDigest/hashv reply value as H; ledger retained-value uses TX1:327, TX2:210', 'YES',
    cone('AdapterRw.SolanaDigest','AspisR1.DGP_HostDigest.hashvInst','RSL.Event.digest'), 'The ledger lists no CLOSED consumer and the NGC_ roots of TX1:327/TX2:210 are not in the cones; the row is reached because every accepted run reads hashv replies as H (bt).', 'RuntimeSha256Value')
add('RuntimeEntrypointAdmission (verifier, 7 fields + 2 wrapper fields)', 'runtime', 'RUN_FRAME: conjuncts 1-2 of NOC_Run5bHost.retained inside S_host.GameFrame; deployed_splitB: hypothesis run.frame; deployed_charge: inside the event Runs (not a hypothesis)', 'YES',
    cone('AspisR1.NOC_Run5bHost.retained','AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission','AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission.entry','AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission.related','AspisR1.AdapterRw.RuntimeEntrypointAdmission','AspisR1.AdapterRw.RuntimeEntrypointAdmission.valid'), 'Whole structure is assumed; only .valid, .entry, .related are projected inside the cones.')
add('RuntimePersistence (CPR_DataPersistence.TwoTransactionLaw)', 'runtime', 'RUN_FRAME: conjunct 3 of NOC_Run5bHost.retained (ordinary := CPG_Projection.ordinary p (key 0), the System-program exclusion)', 'YES',
    cone('AspisR1.CPR_DataPersistence.TwoTransactionLaw','AspisR1.NOC_Run5bHost.retained'), 'Ledger trust row lists no consumers (stale: consumed at the top through run.frame).', 'RuntimePersistence')
add('Allocator (data-only interface)', 'runtime', 'INSTANTIATED (allocator := NNE_AbortIndicator.allocator, ruling (bo)); physical reading falls under AllocatorABICompilerSourceToELF / NOX_ line 5', 'YES',
    cone('AspisR1.S2W_D189Wrappers.Allocator','AspisR1.S2W_D189Wrappers.Allocator.mk','NNE_AbortIndicator.allocator'), '')
add('RuntimeReturnData (nonempty, ruling (ab))', 'runtime', 'META on path: emit_result is called by stage2_owned (TX2:241, reached); RSL.Event.returnData in cone', 'YES (on path; its CLOSED consumer TX2:219 root is not in the cones)',
    cone('RSL.Event.returnData','NNT_Field.r241'), 'The theorem models return data as RSL events; the row is the physical reading of the nonempty emit.', 'RuntimeReturnData', 'ADDED-LEAD 2026-11-04 (ab); OWNER ACCEPTED 2026-11-04')
add('RuntimeReturnDataClear (ruling (am))', 'runtime', 'WINDOW LAW of the (bn) stage2 fission (set_return_data(&[]) at owned.rs:467), consumed by TX2:240 via NMV_ConcreteWindows.root240', 'YES',
    cone('NMV_ConcreteWindows.root240','NVR_TasRoots.field240','RSL.Event.returnData'), 'Ledger still says used:false; stale against ruling (bn) and FIN_240.', 'RuntimeReturnDataClear', 'ADDED-LEAD 2026-11-06 (am); owner class authority 2026-11-04; individual confirmation not recorded')
add('RuntimeMemcmp (688-byte, ruling (ac))', 'runtime', 'META on path: scan_proof_buffer is called by validate_asq8 (TX2:242, NMX_R6_Validation.root in cone)', 'YES (on path; its CLOSED consumer TX2:226 root is not in the cones)',
    cone('NMX_R6_Validation.root'), 'The Lean model reads the 688-byte compare as byte equality; the row is the ELF-level reading of sol_memcmp_.', 'RuntimeMemcmp', 'ADDED-LEAD 2026-11-04 (ac); OWNER ACCEPTED 2026-11-04')
add('RuntimeClockSlotBinding', 'runtime', 'WINDOW LAW (Clock::get at owned.rs:479) via NMV_WindowClock; RSL.Env.clock/Event.clock in cone', 'YES',
    cone('NMV_WindowClock.exact_clock','RSL.Env.clock','RSL.Event.clock','AspisR1.NNH8_Exec.clockFree'), 'fx.clock is a universal Fixed field; NNH8_Exec.clockFree gives model/recorder clock-independence.', 'RuntimeClockSlotBinding', 'ADDED-LEAD-20261105; owner class authority 2026-11-04; individual confirmation not recorded')
add('RuntimeCpiAccountView', 'runtime (Pool)', 'none', 'UNREACHED',
    [], 'Pool CPI sites only; no constant in either cone; would enter only if (aj)(a) puts Pool execution in the game.', 'RuntimeCpiAccountView', 'ADDED-LEAD-20261110 (Stream C (c-a)); owner confirmation not recorded')
add('RuntimeEntrypointAdmission-Pool', 'runtime (Pool)', 'none', 'UNREACHED', [], 'Pool entrypoint only.', 'RuntimeEntrypointAdmission-Pool', 'ADDED-LEAD-20261107 (ap); owner confirmation not recorded')
add('RuntimeCpiReadonlyEntry7', 'runtime (pending)', 'none', 'UNREACHED', [], 'ADDED-PENDING-LEAD, unused.', 'RuntimeCpiReadonlyEntry7', 'PENDING (never admitted)')
add('FixturePdaRuntime', 'runtime (non-vacuity)', 'none', 'UNREACHED', [], 'Zero JHs_/JHw_/JHt_ constants in either cone; op38 is quantified in the theorem.', None, 'ADDED under the standing delegation 2026-10-28 late (non-vacuity only); owner confirmation not recorded')
add('S2TrustedSdkBorrow (15 fields)', 'library', 'BINDER: borrow : S2TrustedSdkBorrow L0 in both kernel statements', 'YES',
    cone('AspisR1.S2Trust.S2TrustedSdkBorrow','AspisR1.S2Trust.S2TrustedSdkBorrow.mk','AspisR1.S2Trust.S2TrustedSdkBorrow.account_data_cell','AspisR1.S2Trust.S2TrustedSdkBorrow.cell_payload'), 'All 15 fields are assumed (the structure is a hypothesis); only account_data_cell and cell_payload are projected inside the cones.', 'S2TrustedSdkBorrow')
add('TrustedStd (slice_copy_from_slice)', 'library', 'BINDER: std : TrustedStd copy in both kernel statements', 'YES',
    cone('AspisR1.S2W_TrustedStd.TrustedStd','AspisR1.S2W_TrustedStd.TrustedStd.slice_copy_from_slice'), 'W1 qualification applies at each use.', 'TrustedStd')
add('TrustedStd (Port1 option_ok_or, result_unwrap32)', 'library', 'none as a hypothesis: AspisR1.Port1_Library.TrustedStd is not in either cone; Port1_Library.std (an instance) is', 'NO as a premise (instantiated by Port1_Library.std); see note',
    cone('AspisR1.Port1_Library.std','AspisR1.Port1_LibrarySource.okOr','AspisR1.Port1_LibrarySource.unwrap32'), 'The Port1 structure itself is not reached; the cone uses the concrete okOr/unwrap32 models (PROPOSED-HM-C covers their std reading).')
add('AeneasExtraction (D188, trace fidelity, narrowed by D188-P3 and (bc))', 'tool', 'INSTANTIATED at the top (a0 := NOC_Run5bHost.a0, native := model) + TOOL: every emitted body in the cones', 'YES',
    cone('AspisR1.S2W_DigestExtraction.AeneasExtraction','AspisR1.S2W_DigestExtraction.AeneasExtraction.mk','AspisR1.S2W_ExtractionBoundary.AeneasExtraction','AspisR1.S2W_ExtractionBoundary.AeneasExtraction.mk','AspisR1.NNG_Candidate136.candidate','AspisR1.NNG_Candidate137.candidate','AspisR1.NNG_Candidate087.candidate','AspisR1.NNG_Candidate094.candidate','AspisR1.NNG_Candidate328.candidate','AspisR1.NNG_ActualCandidate345.candidate','NMX_R3_RegistryRoot.root','NMX_R4_Authentication.root','NMX_R6_Validation.root'), '(bm) emitted-body reclassifications for 136/137/087/094/328/345/234/233/242 have roots in the cones; 241/333/221/330/213 through installed fields.')
add('P6 / Kani association (K-1 narrowing, (br))', 'tool', 'TOOL: native halves of every hybrid row that certifies a function on the deployed path', 'YES', [], 'Not a Lean constant.')
add('NativeContractSemanticTransport (amendment fifth)', 'tool', 'TOOL + LEDGER: consumes_trust of 17 composed rows; 380 direct CLOSED rows', 'YES',
    cone('NLT_CompleteRoot.root'), 'NLT-TX2:065 root in cones; NMN-TX2:064 root (NMN_064.root) not in cones (TX2:064 dropped from the top by (bu)).', 'NativeContractSemanticTransport')
add('P7 compiler/LLVM/platform and pinned Lean/Mathlib/Aeneas base', 'tool', 'TOOL: whole closure', 'YES', [], 'NOX_ lines 1-4 are its concrete SBF instances.')
add('AllocatorABICompilerSourceToELF', 'realization', 'LEDGER consumes_trust of 17 composed rows + ruling (bo) physical reading', 'YES', [], 'NOX_ realization lines (PROPOSED split) make it concrete.', 'AllocatorABICompilerSourceToELF')
add('CheckedVsWrapping (R22)', 'realization', 'TOOL/META: every checked-configuration emitted body in the cones', 'YES', [], 'OPEN; NOX_R22_CONFIG.json lists 24 checked gate modules.')
add('Standard logical axioms', 'logic', 'KERNEL', 'YES', [], 'Walked = collected = {Classical.choice, Quot.sound, propext} for all four roots (L187 final).')
add('Historical checkpoint interfaces (S2X.CheckpointVersionBinding.*, S2W_AuthenticatedInputs...history)', 'historical', 'CONSTRUCTED inside the cones (CPR_DataBinding.binding, CPG_History.on_cuts from RuntimePersistence + game + source proofs); never a hypothesis', 'REACHED AS CONSTRUCTED TERMS, NOT ASSUMED',
    cone('AspisR1.S2X.CheckpointVersionBinding','AspisR1.S2X.CheckpointVersionBinding.mk','AspisR1.S2W_AuthenticatedInputs.CheckpointVersionBinding','AspisR1.S2W_AuthenticatedInputs.CheckpointVersionBinding.mk','AspisR1.CPR_DataBinding.binding','AspisR1.CPG_History.on_cuts'), 'Matches appendix "no additional trust".')
# reviewed transcription items
RT = []
for t in d['reviewed_transcription_inventory']:
    iid = t.get('item') or t.get('id')
    rws = t.get('rows') or ([t['row']] if 'row' in t else [])
    rws = sorted(set(rws) | set(t.get('direct_closed_rows', [])))
    root = t.get('root')
    alt = {'ReviewedTranscription-TX1:344': ['NMV_ConcreteWindows.root344'], 'ReviewedTranscription-TX2:240': ['NMV_ConcreteWindows.root240']}.get(iid, [])
    rr = [allrows.get(x) for x in rws if x in allrows]
    viaroot = [x['row'] for x in rr if x['roots_in_splitB'] or x['roots_in_charge']]
    shared = [x['row'] for x in rr if set(x['roots_in_splitB']) <= {'AspisR1.RPx_Deployed.deployed'} and x['roots_in_splitB']]
    c = cone(*( [root] if root else [])) + [a for a in alt if a in cs]
    reached = bool(c or viaroot)
    RT.append(dict(item=iid, rows=rws, functions=sorted({x['function'] for x in rr}), item_root=root,
                   item_root_or_consumer_in_cones=c, rows_with_root_in_cones=viaroot,
                   reached='YES' if reached else 'UNREACHED',
                   caveat=('only through the shared root AspisR1.RPx_Deployed.deployed' if viaroot and set(viaroot) <= set(shared) and not c else None),
                   ledger_removal_condition=t.get('removal_condition'), ruling=t.get('ruling') or t.get('classification')))
for i in ['ReviewedTranscription-prepared_claim', 'ReviewedTranscription-polynomial', 'ReviewedTranscription-queries_from_pairs']:
    t = ledger_trust[i]; rws = consumers(t); rr = [allrows[x] for x in rws]
    viaroot = [x['row'] for x in rr if x['roots_in_splitB'] or x['roots_in_charge']]
    only_shared = all(set(x['roots_in_splitB']) <= {'AspisR1.RPx_Deployed.deployed'} for x in rr if x['row'] in viaroot)
    RT.append(dict(item=i, rows=rws, functions=sorted({x['function'] for x in rr}), rows_with_root_in_cones=viaroot,
                   roots_in_cones=sorted({y for x in rr for y in x['roots_in_splitB']}),
                   reached='YES' if viaroot else 'UNREACHED',
                   caveat='only through the shared root AspisR1.RPx_Deployed.deployed' if viaroot and only_shared else None, ruling=t.get('ruling')))
for i in ['ReviewedTranscription-POOL324','ReviewedTranscription-POOL345','ReviewedTranscription-POOL296','ReviewedTranscription-POOL320','ReviewedTranscription-POOL223','ReviewedTranscription-POOL332']:
    RT.append(dict(item=i, rows=[], reached='UNREACHED', caveat='Pool rows only; no verifier CLOSED row; enters only if (aj)(a) puts Pool execution in the game'))
ax = [l.rstrip('\n').split('\t') for l in open(f'{S}/out/run/NPI_out_axioms.tsv') if l.strip()]
out = dict(schema='NPI_TRUST_REACH/1', target_established=False,
  basis=dict(source_revision='aceb08e73ed', cones='evidence/replay-l187-20261109/final/L187_AX2_{splitB,charge}', cone_sha256=PIN,
             ledger='evidence/ledger30-20261111/NNN_LEDGER.json.xz', census='NPI_L004 (NPI_out_*.tsv)'),
  method=('A row is reached when a Lean constant that carries it is in both raw ax2 cones (binder, run-frame conjunct, '
          'instantiated structure, window law or field constant), or when a ledger row that consumes it has a root (or an installed '
          'top-field restatement of its root) in the cones, or, for runtime and tool rows, when the frozen function that makes the '
          'call is on the deployed path whose model is in the cones (marked META). Cone membership is exact name membership in the '
          'L187 REACHABLE lists; the same-named-function column for RT items is a heuristic only.'),
  ledger_rows_by_cone=dict(cnt), ledger_roots_total=sum(len(r['root_owners']) for r in d['rows']),
  trust_rows=R, reviewed_transcription=RT,
  axioms=dict(total=len(ax), standard=[a[0] for a in ax if a[2]=='STANDARD'], nonstandard=len([a for a in ax if a[2]=='NONSTANDARD']),
              nonstandard_in_cones=[a[0] for a in ax if a[2]=='NONSTANDARD' and a[3]=='true']))
json.dump(out, open(os.path.join(HERE, 'NPI_TRUST_REACH.json'), 'w'), indent=1)
print(dict(cnt)); print(collections.Counter(x['reached'] for x in RT)); print(len(R))
for x in RT: print(x['item'], x['reached'], x.get('caveat') or '')
