"""PCXF_overlay.py: PCXF_ALL_STATUS.json = PCQI_ALL_STATUS.json (P1i merged over PCUJ) + overlays from P3f, P3h, P3i, P3k, P3l (+ P3g/P1i trust-row classification).
Run: cd evidence; python3 -I -B prov-p6u-20261110/PCXF_overlay.py
Rules (recorded in PCXF_CLASSIFICATIONS.json):
 - a record is only ever moved up from OPEN / HAND_ADAPTED (never down, never between two credited statuses except CONDITIONAL -> DEPENDS_ON_LIBRARY_TRUST when the only outstanding hypothesis is a library item);
 - a new record is added only for a definition proved by an exit-0 scope and absent from the table (AspisR1PublicPreparation.Funs);
 - classes: EQUALITY_PROVED, CONDITIONAL_ON_BINDING (Aspis packet-boundary or instantiation hypotheses), DEPENDS_ON_LIBRARY_TRUST (only library/trust-row items outstanding; row named), OPEN.
"""
import json, re, sys, os, collections
sys.dont_write_bytecode = True
D = 'prov-p6u-20261110'
base = json.load(open('prov-p1i-20261110/PCQI_ALL_STATUS.json'))
mods = base['modules']
STD = {'propext', 'Classical.choice', 'Quot.sound'}

def thm_table(path):
    """[(short, full, statement)] from a Lean file, qualifying by enclosing namespaces."""
    ns = []; out = []
    t = open(path).read()
    lines = t.split('\n')
    i = 0
    cur = None
    for ln in lines:
        m = re.match(r'namespace\s+(\S+)', ln)
        if m: ns.append(m[1]); continue
        m = re.match(r'end\s+(\S+)', ln)
        if m and ns and ns[-1] == m[1]: ns.pop(); continue
        m = re.match(r'(?:private\s+)?(?:theorem|def(?=\s+PRVEq))\s+(\S+)(.*)', ln)
        if m:
            cur = [m[1], '.'.join(ns + [m[1]]) if ns else m[1], m[2]]; out.append(cur); continue
        if cur is not None:
            if re.match(r'(theorem|def|lemma|noncomputable|namespace|end|section|open|set_option|instance|structure|abbrev|inductive|/--)', ln): cur = None
            else: cur[2] += '\n' + ln
    return [(a, b, c.split(':=')[0]) for a, b, c in out]

def match_defs(stmt, modlist):
    toks = set(re.findall(r"[A-Za-z_][\w.'«»]*", stmt))
    hit = [(m, n) for m in modlist for n in mods[m] if n in toks]
    hit.sort(key=lambda x: -len(x[1]))
    return hit

def receipt(dirp, scope):
    p = f'{dirp}/{scope}/receipt.json'
    r = json.load(open(p))
    ax = ' '.join(r.get('print_axioms') or [])
    names = set(re.findall(r'depends on axioms: \[([^\]]*)\]', ax.replace('\n', ' ')))
    used = set()
    for s in names: used |= {x.strip() for x in s.replace('\n', ' ').split(',') if x.strip()}
    assert r['exit_status'] == 0, (p, r['exit_status'])
    assert not (used - STD), (p, used - STD)
    assert 'sorryAx' not in ax
    return p, dict(exit=r['exit_status'], wall=round(r['wall_seconds'], 1), rss=int(r['peak_rss_kib']), swaps=r['swaps'], axioms=sorted(used))

log = []
RANK = {'OPEN': 0, 'HAND_ADAPTED': 0, 'NO_FROZEN_COUNTERPART': 0, 'CONDITIONAL_ON_BINDING': 1, 'DEPENDS_ON_LIBRARY_TRUST': 1, 'EQUALITY_DOMAIN': 2, 'EQUALITY_PROVED': 2, 'RECEIPTED': 2}
def put(module, dfn, status, thm, pfile, phase, scope, phdir, config='ON', emission=None, cond=None, trust=None, extra=None, tool='extended'):
    rec = mods[module].get(dfn)
    prev = rec['status'] if rec else None
    if rec and RANK.get(prev, 0) >= 2 and prev != status:
        log.append(dict(module=module, definition=dfn, action='SKIPPED_ALREADY_CREDITED', previous=prev, wanted=status, phase=phase)); return
    if rec and prev == status == 'EQUALITY_PROVED':
        log.append(dict(module=module, definition=dfn, action='SKIPPED_ALREADY_PROVED', previous=prev, phase=phase)); return
    rp, rinfo = receipt(phdir, scope)
    new = dict(rec or dict(module=module, definition=dfn, base_status=None, fresh_emission=None, aeneas_tool=tool, source_revision='frozen 4bb3b3f (fresh emission)'))
    new.update(status=status, open_reason=None, theorem=thm, proving_file=pfile, receipt=rp, configuration=config, required_configuration=config, decided_by=phase, previous_status=prev, pcxe_scope=rinfo)
    if emission: new['fresh_emission'] = emission
    if cond: new['condition'] = cond
    if trust: new['trust_rows'] = trust
    if extra: new.update(extra)
    mods[module][dfn] = new
    log.append(dict(module=module, definition=dfn, action='SET', previous=prev, status=status, phase=phase, theorem=thm, file=pfile, scope=scope))

AD = 'Retained: the Ext callees of the emission equal their gate counterparts (Bound); the deployed Ops instance equals an Ops with Bound is not shown here.'
# ---------------- P3f
d = 'prov-p3f-20261110'
f = f'{d}/PRVEq_S1NativeCompactModelV1_okor_f1.lean'
for s, fl, dfn in [('okor', f, 'AspisS1NativeCompact.core.option.Option.ok_or')]:
    th = {a: b for a, b, c in thm_table(f)}
    put('S1NativeCompactModelV1', dfn, 'EQUALITY_PROVED', th['PRVEq.S1NativeCompactModelV1.core.option.Option.ok_or_f1'], f, 'P3f', 'PCVF_L001', d)
f = f'{d}/PRVEq_AdapterRwModel_k1.lean'; th = {a: b for a, b, c in thm_table(f)}
for k, dfn in [('ProgramError_clone_inst', 'AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone'), ('SolanaDigest_clone_inst', 'AdapterRw.SolanaDigest.Insts.CoreCloneClone'), ('SolanaDigest_copy_inst', 'AdapterRw.SolanaDigest.Insts.CoreMarkerCopy'),
               ('SolanaDigest_digest32_inst', 'AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32'), ('Pubkey_eq_inst', 'AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey'), ('observer_eq', 'AdapterRw.observer'),
               ('first_decoded_eq', 'AdapterRw.first_decoded'), ('data_len_eq', 'AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len'), ('require_verifier_checkpoint_eq', 'AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint')]:
    put('AdapterRwModel', dfn, 'CONDITIONAL_ON_BINDING', th[k], f, 'P3f', 'PCVF_L009', d, cond='for every ops and Ext with Bound ops x: emission text with the externals replaced by x equals the gate at ops. ' + AD, trust=['HM-A (SDK types Pubkey/Hash/ProgramError)'])
f = f'{d}/PRVEq_Port5Q2_ReaderWeights_k1.lean'; th = {a: b for a, b, c in thm_table(f)}
put('Port5Q2_ReaderWeights', 'AspisR1.Port5Q2_ReaderWeights.weights_loop', 'CONDITIONAL_ON_BINDING', th['loop_eq'], f, 'P3f', 'PCVF_L010', d, cond='loop and body equal the gate at read := fresh Reader.k with no hypothesis; the gate is a parametric record instantiated at the fresh read function (instantiation not shown for the deployed gate use)')
put('Port5Q2_ReaderWeights', 'AspisR1.Port5Q2_ReaderWeights.weights', 'CONDITIONAL_ON_BINDING', th['weights_eq'], f, 'P3f', 'PCVF_L010', d, cond='hypothesis: the emission Vec IterMut external equals the gate hand model intoIter (library item); plus the read := fresh Reader.k instantiation', trust=['HM-B (core slice/array iterator models)'])
f = f'{d}/PRVEq_NMT_k1.lean'; th = {a: b for a, b, c in thm_table(f)}
put('NMT_first.Funs', 'NMT_first.SolanaDigest.Insts.Aspis_coreDigestDigest32.digest', 'CONDITIONAL_ON_BINDING', th['PRVEq.NMT_first.digest_k1'], f, 'P3f', 'PCVF_L012', d, cond='the NMT gate takes its opaque callees (NMT_call_4 Hash.to_bytes, NMT_call_5 hashv) as parameters; fresh text takes them as parameters; rfl for all callees. Binding of the parameters to frozen items is at the instantiation.', trust=['HM-A (SDK Hash)'])
put('NMT_stage1_owned.Funs', 'NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data', 'CONDITIONAL_ON_BINDING', th['PRVEq.NMT_stage1_owned.data_k1'], f, 'P3f', 'PCVF_L012', d, cond='NMT_call_10 parameter; binding at the instantiation')
f = f'{d}/PRVEq_Port3_closures_k2.lean'; th = {a: b for a, b, c in thm_table(f)}
PORT = 'PCVF_E005 (OFF emission; gate closure_4.closure call_mut carries wrapping_mul/add)'
for a, b, c in thm_table(f):
    m = re.fullmatch(r'PRVEq\.Port3_k2\.eq_(\d+)', b)
    if not m: continue
    i = int(m[1]); hit = [h for h in match_defs(c, ['Port3_NativeGeometryBody'])]
    assert hit, (b)
    # the gate-side name is the RHS; take the longest key present in the statement after '='
    rhs = c.split('=', 1)[1] if '=' in c else c
    hit = [h for h in match_defs(rhs, ['Port3_NativeGeometryBody'])]
    dfn = hit[0][1]
    st_ = 'EQUALITY_PROVED' if (i <= 3 or i >= 12) else 'CONDITIONAL_ON_BINDING'
    put('Port3_NativeGeometryBody', dfn, st_, b, f, 'P3f', 'PCVF_L015', d, config='OFF', emission=PORT, cond=None if st_ == 'EQUALITY_PROVED' else 'Bound ops x: op0 = from_fn external, op5 = M31 eq, op6 = M31 zero (binding at the instantiation; from_fn is the opaque core.array.from_fn, HM-M proof item)',
        extra=dict(basis_class='OFF_EMISSION_PCVF_E005', configuration_note='gate carries wrapping operators only in closure_4.closure call_mut; the remaining 17 have no arithmetic'))
f = f'{d}/PRVEq_CompactOff_k3.lean'; th = {a: b for a, b, c in thm_table(f)}
for k in ['OFF_SEMANTIC', 'OFF_Y1', 'OFF_INACTIVE', 'OFF_FOLDED_ROOT', 'OFF_ROUND1']:
    put('CurrentCompactCallerModelV1', f'AspisR1CurrentCaller.compact.{k}', 'CONDITIONAL_ON_BINDING', th[f'{k}_eq'], f, 'P3f', 'PCVF_L017', d, emission='PCQF_E006', cond='under Bound ops (op12 = ok OFF_SEMANTIC, op13 = COMPACT_SEMANTIC, op14 = COMPACT_Y1, op21 = OFF_ROUND0, all fresh constants): fresh = gate; binding at the instantiation')
# ---------------- P3h
d = 'prov-p3h-20261110'
H = [('R1CandidateWideParserSource', 'AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes', 'PRVEq_PCVH_R1CandidateWideParserSource_k1.lean', 'PCVH_L008', 'PRVEq.R1CandidateWideParserSource_k1.field.wide_exact.WideExact.from_le_bytes'),
     ('AspisR1EbyKFinish.Funs', 'AspisR1EbyKFinish.field.wide_exact.WideExact.from_limbs', 'PRVEq_AspisR1EbyKFinish_Funs_n1.lean', 'PCVH_L010', 'PRVEq.AspisR1EbyKFinish.Funs_n1.field.wide_exact.WideExact.from_limbs'),
     ('AspisR1QueryGeometryActual.Funs', 'AspisR1QueryGeometryActual.fast_domain.TABLE_A', 'PRVEq_AspisR1QueryGeometryActual_Funs_m1.lean', 'PCVH_L020', 'PRVEq.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_A'),
     ('AspisR1QueryGeometryActual.Funs', 'AspisR1QueryGeometryActual.fast_domain.TABLE_B', 'PRVEq_AspisR1QueryGeometryActual_Funs_m1.lean', 'PCVH_L020', 'PRVEq.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_B'),
     ('CurrentCompactCallerModelV1', 'AspisR1CurrentCaller.compact.LOGICAL_Y1', 'PRVEq_CurrentCompactCallerModelV1_n1.lean', 'PCVH_L011', 'PRVEq.CurrentCompactCallerModelV1_n1.compact.LOGICAL_Y1'),
     ('CurrentCompactCallerModelV1', 'AspisR1CurrentCaller.compact.SPLIT', 'PRVEq_CurrentCompactCallerModelV1_n2.lean', 'PCVH_L012', 'PRVEq.CurrentCompactCallerModelV1_n2.compact.SPLIT'),
     ('FinishCandidateExplicitOps', 'AspisR1FinishRelationCurrent.transport.Variant.folds', 'PRVEq_FinishCandidateExplicitOps_n1.lean', 'PCVH_L013', 'PRVEq.FinishCandidateExplicitOps_n1.transport.Variant.folds'),
     ('Stage2ContinuationTypes', 'AspisR1Stage2.verifier.Reader', 'PRVEq_Stage2ContinuationTypes_n2.lean', 'PCVH_L022', 'PRVEq.Stage2ContinuationTypes_n2.verifier.Reader.equiv')]
for m, dfn, fl, sc, thm in H:
    tt = {b for a, b, c in thm_table(f'{d}/{fl}')}
    assert thm in tt, (thm, sorted(tt)[:5])
    put(m, dfn, 'EQUALITY_PROVED', thm, f'{d}/{fl}', 'P3h', sc, d, extra=dict(record_kind='ISOMORPHISM_OF_TYPES_DECLARATIONS (Equiv, constructor-wise or structure-wise)') if thm.endswith('.equiv') else None)
# ---------------- P3i
d = 'prov-p3i-20261110'
f = f'{d}/PRVEq_S1NativeCompactExpand_i1.lean'; th = {a: b for a, b, c in thm_table(f)}
for k, dfn in [('expand_semantic_i1', 'compact.expand_semantic'), ('expand_semantic_loop_i1', 'compact.expand_semantic_loop'), ('expand_semantic_loop.body_i1', 'compact.expand_semantic_loop.body')]:
    put('S1NativeCompactModelV1', 'AspisS1NativeCompact.' + dfn, 'CONDITIONAL_ON_BINDING', th['PRVEq.S1NC.' + k], f, 'P3i', 'PCVI_L002', d, cond='for every ops: emission text with the external compact.expand_values replaced by ops.expandValues equals the gate at ops; not shown: the deployed ops.expandValues equals the frozen compact.expand_values (Aspis item)')
f = f'{d}/PRVEq_Port23PUSH_Source_i1.lean'; th = {a: b for a, b, c in thm_table(f)}
for k, dfn in [('PRVEq.Port23PUSH_Source.verifier.update_residue_row_i1', 'Port23PUSH.verifier.update_residue_row'), ('PRVEq.Port23PUSH_Source.verifier.BatchedWeights.push_i1', 'Port23PUSH.verifier.BatchedWeights.push')]:
    put('Port23PUSH_Source', dfn, 'DEPENDS_ON_LIBRARY_TRUST', th[k], f, 'P3i', 'PCVI_L003', d, cond='for every f : ArrayIntoIter, emission text with the MutAArray IterMut into_iter replaced by f equals the gate at f; the only outstanding item is that f is the library into_iter',
        trust=['HM-B (core slice and array iterator models: MutAArray IterMut into_iter, Array into_iter)'])
f = f'{d}/PRVEq_NMT_stage1_owned_i1.lean'; th = {a: b for a, b, c in thm_table(f)}
put('NMT_stage1_owned.Funs', 'NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned', 'CONDITIONAL_ON_BINDING', th['PRVEq.NMT_stage1_owned.stage1_owned_i1'], f, 'P3i', 'PCVI_L004', d, cond='for all 17 callee parameters NMT_call_0..16 (order table in the file header): emission text with callees replaced by the parameters equals the gate; binding at the instantiation', trust=['HM-A (SDK types among the callees)'])
f = f'{d}/PRVEq_RPz7_FIp_NativeDots_i9.lean'; th = {a: b for a, b, c in thm_table(f)}
for k, dfn in [('four_dots_one_loop0_loop0.body_i4', 'four_dots_one_loop0_loop0.body'), ('four_dots_one_loop0_loop0_i4', 'four_dots_one_loop0_loop0'), ('four_dots_one_loop0.body_i4', 'four_dots_one_loop0.body'), ('four_dots_one_loop0_i4', 'four_dots_one_loop0')]:
    put('RPz7_FIp_NativeDots', 'AspisR1.FIp_NativeDots.fast_dots.' + dfn, 'EQUALITY_PROVED', th['PRVEq.RPz7_FIp_NativeDots.' + k], f, 'P3i', 'PCVI_L019', d)
# ---------------- P3k
d = 'prov-p3k-20261110'
f = f'{d}/PRVEq_AdapterStage1_k4.lean'; th = {a: b for a, b, c in thm_table(f)}; tn = {a: b for a, b, c in thm_table(f)}
EMI = {'s1': 'PCVJ_E004', 's2': 'PCVJ_E005', 'c': 'PCVJ_E002'}
HMA = ['HM-A (SDK types Pubkey/Hash/ProgramError; solana_sdk_ids bpf_loader_upgradeable.id is not named in HM-A today)']
put('AdapterRwModel', 'AdapterRw.r1_pool_adapter.owned.stage1_owned', 'CONDITIONAL_ON_BINDING', th['r1_pool_adapter_owned_stage1_owned_eq'], f, 'P3k', 'PCVK_L027', d, emission=EMI['s1'], cond='parametric-record route: for every ops and Ext x with Bound ops x (16 callees): fresh stage1_owned x = gate stage1_owned ops. Bound is satisfiable (bound_exists); the deployed Ops is not shown to satisfy Bound.', trust=HMA)
put('AdapterRwModel', 'AdapterRw.r1_pool_adapter.owned.OwnedAccount.data', 'CONDITIONAL_ON_BINDING', th['data_eq'], f, 'P3k', 'PCVK_L027', d, emission=EMI['s1'], cond='as stage1_owned', trust=HMA)
f = f'{d}/PRVEq_AdapterStage2_k9.lean'; th = {a: b for a, b, c in thm_table(f)}
for k, dfn in [('r1_pool_adapter_owned_stage2_owned_eq', 'AdapterRw.r1_pool_adapter.owned.stage2_owned'), ('r1_pool_adapter_owned_validate_asq8_eq', 'AdapterRw.r1_pool_adapter.owned.validate_asq8'), ('r1_pool_adapter_owned_authenticate_asq8_accounts_eq', 'AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts')]:
    put('AdapterRwModel', dfn, 'CONDITIONAL_ON_BINDING', th[k], f, 'P3k', 'PCVK_L026', d, emission=EMI['s2'], cond='parametric-record route: 38 callees plus Hash bound (Bound ops x); hashv and Hash.to_bytes bound through h43/h42; the deployed Ops is not shown to satisfy Bound', trust=HMA)
f = f'{d}/PRVEq_CallerPrepTx1_k3.lean'; th = {a: b for a, b, c in thm_table(f)}
for k, dfn in [('verifier_candidate_prepare_eq', 'verifier.candidate.prepare'), ('verifier_candidate_tx1_eq', 'verifier.candidate.tx1'), ('c_logical_semantic', 'compact.LOGICAL_SEMANTIC')]:
    put('CurrentCompactCallerModelV1', 'AspisR1CurrentCaller.' + dfn, 'CONDITIONAL_ON_BINDING', th[k], f, 'P3k', 'PCVK_L030', d, emission=EMI['c'], cond='parametric-record route: 17 callees plus six Ops fields bound to fresh definitions (Bound ops x); the deployed Ops is not shown to satisfy Bound', trust=['HM-A (SDK types among the callees)'])
# ---------------- P3l
d = 'prov-p3l-20261110'
f = f'{d}/PRVEq_VTop_l1.lean'; th = {a: b for a, b, c in thm_table(f)}
for k, dfn in [('eq_tx2_common', 'tx2_common'), ('eq_tx2_authenticated', 'tx2_authenticated')]:
    tn_ = [b for a, b, c in thm_table(f) if a.endswith(k)][0]
    put('VTop_Model', 'VTop_Stages.verifier.candidate.' + dfn, 'CONDITIONAL_ON_BINDING', tn_, f, 'P3l', 'PCVL_L004', d, emission='PCVJ_E002', cond='for every Ext (the 23 externals of the PCVJ_E002 emission as fields) and every gate ops with Bound ops x: fresh = gate at all arguments. The Ext fields (packet boundaries of the top design plus library items) are not related to frozen items here; the deployed Ops instance is not shown to satisfy Bound.', trust=['HM-B/HM-C/HM-D (library externals in Ext: slice PartialEq, Result.map_err, Iter.any)'])
# PublicPreparation: per-definition dependency closure on the two callees
f = f'{d}/PRVEq_PP_l4.lean'; txt = open(f).read()
fresh = txt.split('namespace PRVFresh_AspisR1PublicPreparation_Funs_l4', 1)[1].split('\nend PRVFresh_AspisR1PublicPreparation_Funs_l4', 1)[0]
chunks = re.split(r'(?m)^(?:/--.*?-/\n)?(?:@\[[^\]]*\]\n)?def\s+', fresh, flags=re.S)[1:]
bodies = {}
for ch in chunks:
    nm = re.match(r'(\S+)', ch)[1]; bodies[nm] = ch
deps = {n: set() for n in bodies}
direct = {}
for n, b in bodies.items():
    direct[n] = set()
    if re.search(r'Public\.public_bytes', b): direct[n].add('public_bytes')
    if re.search(r'map_err', b): direct[n].add('map_err')
    for m2 in bodies:
        if m2 != n and re.search(r'(?<![\w.])' + re.escape(m2) + r'(?![\w])', b): deps[n].add(m2)
def closure(n, seen=None):
    seen = seen if seen is not None else set()
    out = set(direct[n])
    for m2 in deps[n]:
        if m2 not in seen:
            seen.add(m2); out |= closure(m2, seen)
    return out
ppth = {b.split('Funs_l4.', 1)[1] if 'Funs_l4.' in b else b: b for a, b, c in thm_table(f)}
PPM = 'AspisR1PublicPreparation.Funs'
pp_info = {}
for n in bodies:
    cl = closure(n)
    key = 'AspisR1PublicPreparation.' + n
    thm = ppth.get(n)
    if thm is None: continue
    pp_info[n] = sorted(cl)
    rows = []
    if 'public_bytes' in cl: rows.append('ReviewedTranscription-PublicPreparation.public_bytes (ADDED-LEAD-20261110; evidence/public-bytes-20261110, NPL_PublicBytes.gate_eq, gate_total_length)')
    if 'map_err' in cl: rows.append('HM-C (Option/Result combinators: core.result.Result.map_err)')
    st_ = 'DEPENDS_ON_LIBRARY_TRUST' if rows else 'EQUALITY_PROVED'
    put(PPM, key, st_, thm, f, 'P3l', 'PCVL_L007', d, emission='PCVL_E003', trust=rows or None,
        cond=('callee names resolve to the gate definitions by name: ' + ', '.join(sorted(cl)) + '. The gate Public.public_bytes was emitted from the mirror crate aspis_r1_public_preparation, not the frozen file (ReviewedTranscription row, not a library row); counted as dependent, not proved.') if rows else None,
        extra=dict(pp_callee_closure=sorted(cl)))
# ---------------- P3g / P1i triage: DEPENDS_ON_LIBRARY_TRUST (HM-B) for WideToBytes
for m, dfn in [('AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions', 'AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes'),
               ('AspisR1WideToBytesSource.Funs', 'AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes'),
               ('AspisR1WideToBytesSource.Funs', 'AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes_loop'),
               ('AspisR1WideToBytesSource.Funs', 'AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes_loop.body')]:
    rec = mods[m][dfn]; prev = rec['status']
    assert prev == 'OPEN', (m, dfn, prev)
    rec.update(status='DEPENDS_ON_LIBRARY_TRUST', previous_status=prev, theorem=None, proving_file=None, receipt=None, decided_by='P3g (PCVG_REMAINING.json triage, lead ruling)', trust_rows=['HM-B (core slice iterator model: chunks_exact_mut, ChunksExactMut::next)'],
               open_reason=None, condition='only obstacle recorded in PCXE_NOT_ATTEMPTED_23: the gate is written against P6ToBytes.StdModel iterators while the emission uses core.slice.iter.ChunksExactMut; no Lean equality was attempted or proved. The Aspis-side loop-body arithmetic is not separated from the library part and no proof of it exists.',
               aspis_side_residue_not_separated=True)
    log.append(dict(module=m, definition=dfn, action='SET', previous=prev, status='DEPENDS_ON_LIBRARY_TRUST', phase='P3g'))
# P3d constant binding: the only outstanding item is the cross-crate constant encoding row
rec = mods['RPu_FIq_Native07']['FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim']
assert rec['status'] == 'CONDITIONAL_ON_BINDING', rec['status']
rec.update(status='DEPENDS_ON_LIBRARY_TRUST', previous_status='CONDITIONAL_ON_BINDING', trust_rows=['CrossCrateConstantEncoding (link between an Aeneas external axiom of type Result X and a transparent value: ok <gate value>)'],
           condition='constant binding (external := ok <gate/fresh value>); the only outstanding item is the cross-crate constant encoding link, which is a trust-row item, not a library function; recorded in this class by the P6 refresh brief')
log.append(dict(module='RPu_FIq_Native07', definition='FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim', action='SET', previous='CONDITIONAL_ON_BINDING', status='DEPENDS_ON_LIBRARY_TRUST', phase='P6 refresh (P3d result)'))
# totals
tot = collections.Counter(r['status'] for dd in mods.values() for r in dd.values())
base['schema'] = 'PCXF_ALL_STATUS/1'
base['totals'] = dict(tot); base['n_definitions'] = sum(tot.values())
base['rule'] = 'PCQI_ALL_STATUS (P1i over PCUJ) + P3f/P3h/P3i/P3k/P3l overlays and the P3g HM-B triage; see PCXF_overlay.py and PCXF_OVERLAY_LOG.json. ' + base['rule'][:0]
base['sources'] = list(base['sources']) + ['PCVF_STATUS.json (P3f)', 'PCVH_STATUS.json (P3h)', 'PCVI_STATUS.json (P3i)', 'PCVK_STATUS.json (P3k)', 'PCVL_STATUS.json (P3l)', 'PCVG_REMAINING.json (P3g triage)', 'PCVJ (P1j): no definition credited']
json.dump(base, open(f'{D}/PCXF_ALL_STATUS.json', 'w'))
json.dump(dict(schema='PCXF_OVERLAY_LOG/1', log=log, pp_callee_closure=pp_info), open(f'{D}/PCXF_OVERLAY_LOG.json', 'w'), indent=1)
c = collections.Counter((x['action'], x.get('status')) for x in log)
print(dict(tot)); print(c)
print('PP closure:', {n: v for n, v in pp_info.items()})
