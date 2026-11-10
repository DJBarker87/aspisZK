#!/usr/bin/env python3
"""PCXL_recount.py: headline recount by each job's STATUS CLASSES (not theorem shape).

Usage: python3 -I PCXL_recount.py [--ref research] [--job dir:PREFIX ...] [--out PCXL_COUNTS.json]
Reads ONLY committed files through `git show <ref>:<path>` (stdlib only). Script work, no Lean, no host.

Split (Stream A lead, binding):
  SETTLED     = EQUALITY_PROVED (unconditional fresh = gate, no trust row named), RECEIPTED_PIN_EQUAL,
                RECEIPTED_SELECTED_MASK_PROBE, EQUALITY_PROVED_P1N (baseline), and OFF_EMISSION_WRAPPING where the Stream A lead
                accepted it (FIn_WeightsFuns, NGD slot_offset records).
  NOT SETTLED = OPEN and all variants, RECEIPTED_NO_PIN_EQUAL_EVIDENCE, RECEIPTED_TEXT_DIFFERS, EQUALITY_NOT_REPLAYED_IN_L187.
  OTHER       = everything else (CONDITIONAL_ON_BINDING, DEPENDS_ON_LIBRARY_TRUST, TYPE_ISOMORPHISM, EQUALITY_DOMAIN,
                REFINEMENT_LOOP_RETURN, GATE_ONLY_HELPER, HAND_ADAPTED, NO_FROZEN_COUNTERPART at baseline, ...).
Method: P6w baseline (PCXH_PROVENANCE per_definition_class, PCXH_ROW_TABLES) then one adapter per merged job, in merge order.
Each adapter maps the job's STATUS records to (gate module|definition, class); lead_corrections / lead_classes of each STATUS
are applied. A STATUS key that is not in the baseline is UNMATCHED and listed, never guessed. Where a STATUS lists no
per-definition keys (PCQL, PCVX) the keys come from the job's exit-0 standard-axioms theorems of shape `@FRESH = @GATE`
(proof evidence only), restricted to the modules/claims the STATUS names; the class is the STATUS's.
"""
import json, re, subprocess, sys, collections, argparse

ap = argparse.ArgumentParser()
ap.add_argument('--ref', default='research')
ap.add_argument('--job', action='append', default=[], help='extra later job dir:PREFIX (generic adapter: STATUS lead_classes)')
ap.add_argument('--out', default=None)
ap.add_argument('--assume-settled', default=None, help='JSON list of cone keys treated as SETTLED; prints rows settled-only of 599')
args = ap.parse_args() if __name__ == '__main__' else ap.parse_args([])
REF = args.ref
E = 'evidence/'


def show(p):
    return subprocess.run(['git', 'show', REF + ':' + p], capture_output=True, check=True).stdout.decode()


def tryshow(p):
    r = subprocess.run(['git', 'show', REF + ':' + p], capture_output=True)
    return r.stdout.decode() if r.returncode == 0 else None


def J(p):
    return json.loads(show(p))


SETTLED_BASE = {'EQUALITY_PROVED', 'EQUALITY_PROVED_P1N', 'RECEIPTED_PIN_EQUAL', 'RECEIPTED_SELECTED_MASK_PROBE'}
SETTLED_JOB = {'EQUALITY_PROVED_JOB', 'OFF_EMISSION_WRAPPING_ACCEPTED'}
SET = SETTLED_BASE | SETTLED_JOB
NOTSET = {'RECEIPTED_NO_PIN_EQUAL_EVIDENCE', 'RECEIPTED_TEXT_DIFFERS', 'OPEN_NOT_REDERIVABLE', 'OPEN', 'OPEN_RECONSTRUCTED_SOURCE',
          'EQUALITY_NOT_REPLAYED_IN_L187', 'CANNOT_EXTRACT', 'NO_FRESH_EMISSION', 'COMPARE_FAILED'}
STD = {'propext', 'Classical.choice', 'Quot.sound'}

PCXH_P = J(E + 'prov-p6w-20261110/PCXH_PROVENANCE.json')
PCXH_R = J(E + 'prov-p6w-20261110/PCXH_ROW_TABLES.json')
PCXF_P = J(E + 'prov-p6u-20261110/PCXF_PROVENANCE.json')
PCXF_R = J(E + 'prov-p6u-20261110/PCXF_ROW_TABLES.json')
TRUST = J(E + 'prov-p6u-20261110/PCXF_TRUST_NAMING.json')
base = dict(PCXH_P['per_definition_class'])
cone = {f'{m}|{d}' for m, mm in PCXF_P['modules'].items() for d, r in mm['definitions'].items() if r.get('in_splitB_cone')}
rowdefs = {row: [f'{m}|{d}' for m, ds in mods.items() for d in ds] for row, mods in PCXF_R['row_to_module_to_definitions'].items()}
byname = collections.defaultdict(list)
for k in base:
    m, d = k.split('|', 1)
    byname[d].append(m)


def kind(c):
    return 'S' if c in SET else 'N' if c in NOTSET else 'O'


def row_status(cls):
    out = {}
    for row, ds in rowdefs.items():
        t = collections.Counter(kind(cls[k]) if k in cls else 'U' for k in ds)
        out[row] = t
    return out


def numbers(cls):
    c = collections.Counter(cls[k] for k in cone)
    s = sum(v for k, v in c.items() if k in SET)
    n = sum(v for k, v in c.items() if k in NOTSET)
    other = {k: v for k, v in c.items() if k not in SET and k not in NOTSET}
    rs = row_status(cls)
    settled_only = sum(1 for t in rs.values() if t['N'] == 0 and t['O'] == 0 and t['U'] == 0 and t['S'] > 0)
    return dict(cone_definitions=sum(c.values()), settled=s, not_settled=n, other=sum(other.values()), other_classes=other,
                settled_classes={k: v for k, v in c.items() if k in SET}, not_settled_classes={k: v for k, v in c.items() if k in NOTSET},
                rows_settled_only=settled_only)


b0 = numbers(base)
assert b0['settled'] == PCXH_P['SETTLED'] and b0['not_settled'] == PCXH_P['NOT_SETTLED'] and b0['other'] == 65, ('baseline mismatch', b0)
assert b0['rows_settled_only'] == PCXH_R['counts_PCXH']['ALL_REACHED_DEFINITIONS_SETTLED'], ('row baseline mismatch', b0)

# ---------------------------------------------------------------- shape evidence (proof evidence only)
THM = re.compile(r'^theorem\s+(\S+)\s*:\s*@(\S+)\s*=\s*@(\S+)\s*:=', re.M)
AX = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def shape_credits(d, pre):
    """exit-0 standard-axioms theorems `@FRESH = @GATE` of a job -> {gate key: theorem}, plus unmatched list."""
    jd = E + d + '/'
    att = [json.loads(l) for l in show(jd + pre + '_ATTEMPTS.jsonl').splitlines() if l.strip()]
    cred = {}; unm = []
    for e in att:
        if e.get('event') != 'result' or e.get('kind') != 'lean' or e.get('exit_status') != 0:
            continue
        pa = e.get('print_axioms') or []
        if isinstance(pa, str):
            try: pa = json.loads(pa)
            except Exception: pa = [pa]
        ok = {}
        for ln in pa:
            for m in AX.finditer(ln):
                ax = {a.strip() for a in (m.group(2) or '').replace('\n', ' ').split(',') if a.strip()}
                ok[m.group(1)] = ax <= STD
        src = None
        for s in e.get('sources', []):
            if s.endswith('.lean') and e['module'] in s:
                src = tryshow(jd + e['attempt'] + '/sources/' + s) or tryshow(jd + s.split('/')[-1])
        if src is None: src = tryshow(jd + e['module'] + '.lean')
        if src is None:
            unm.append(dict(scope=e['attempt'], reason='source not found')); continue
        imps = re.findall(r'^import\s+(\S+)', src, re.M)
        gmods = [i for i in imps if i != 'Aeneas' and not i.startswith(('PRV', 'PCV', 'PCQ'))]
        for m in THM.finditer(src):
            name, fresh, gate = m.groups()
            if not ok.get(name): continue
            cands = byname.get(gate, [])
            if len(cands) > 1: cands = [c for c in cands if c in gmods] or cands
            if len(cands) == 0: unm.append(dict(theorem=name, gate=gate, reason='UNMATCHED: definition not in PCXH baseline universe')); continue
            if len(cands) > 1: unm.append(dict(theorem=name, gate=gate, modules=cands, reason='AMBIGUOUS gate module')); continue
            cred[f'{cands[0]}|{gate}'] = name
    return cred, unm


def resolve(mod, name):
    """gate module + definition name (with or without module prefix) -> baseline key or None (exactly one)."""
    c = [k for k in base if k.split('|', 1)[0] == mod and (k.split('|', 1)[1] == name or k.split('|', 1)[1].split('.', 1)[-1] == name)]
    if len(c) == 1: return c[0]
    c2 = [k for k in c if k.split('|', 1)[1] == name]
    return c2[0] if len(c2) == 1 else None


# ---------------------------------------------------------------- state
cls = dict(base)
log = []          # per-job records
conflicts = []
unmatched = []
hm_rows = collections.defaultdict(list)   # HM row -> [{key, job, class, note}]
hm_job_level = []


def assign(job, k, new, why, hm=None, shape=False):
    """apply class `new` to baseline key k. Returns the change dict or None."""
    if k not in cls:
        unmatched.append(dict(job=job, key=k, reason='UNMATCHED: key not in PCXH baseline universe', class_wanted=new)); return None
    cur = cls[k]
    if hm:
        for h in hm: hm_rows[h].append(dict(key=k, job=job, class_=new, in_cone=k in cone))
    if cur == new: return dict(key=k, was=cur, now=new, why=why, changed=False, in_cone=k in cone)
    kc, kn = kind(cur), kind(new)
    if kc == 'S' and kn == 'S':
        return dict(key=k, was=cur, now=new, why=why, changed=False, in_cone=k in cone)
    if shape and kc == 'O':
        conflicts.append(dict(job=job, key=k, kept=cur, later_says=new, rule='theorem-shape credit never discharges an other-class condition (binding/domain/library)', why=why)); return None
    if kc == 'S' and kn != 'S':
        conflicts.append(dict(job=job, key=k, kept=cur, later_says=new, rule='earlier proof not withdrawn: strongest proved class wins', why=why)); return None
    if kc == 'O' and kn == 'N':
        conflicts.append(dict(job=job, key=k, kept=cur, later_says=new, rule='open label does not weaken an already classed other-class key', why=why)); return None
    if kc == 'O' and kn == 'S':
        conflicts.append(dict(job=job, key=k, was=cur, now=new, rule='strongest proved class wins (other -> settled); STATUS records an unconditional equality', why=why))
    cls[k] = new
    return dict(key=k, was=cur, now=new, why=why, changed=True, in_cone=k in cone)


def run_job(job, pre, d, fn):
    before = numbers(cls)
    recs, notes, mapping = fn()
    changes = [r for r in recs if r and r['changed']]
    after = numbers(cls)
    log.append(dict(job=job, prefix=pre, dir=d, adapter_mapping=mapping, notes=notes,
                    records_mapped=len([r for r in recs if r]), changes=len(changes), changes_in_cone=sum(1 for c in changes if c['in_cone']),
                    unchanged_already_in_class=len([r for r in recs if r and not r['changed']]),
                    change_list=changes, after=after,
                    delta=dict(settled=after['settled'] - before['settled'], not_settled=after['not_settled'] - before['not_settled'],
                               other=after['other'] - before['other'], rows_settled_only=after['rows_settled_only'] - before['rows_settled_only'])))
    print(f"{pre:5} {job:8} mapping {mapping}  changes {len(changes)}  delta {log[-1]['delta']}  -> {after['settled']}/{after['not_settled']}/{after['other']} rows {after['rows_settled_only']}")


def S(pre, d, f):
    return J(E + d + '/' + pre + '_' + f + '.json')


# ---------------------------------------------------------------- adapters
def a_PCQL():
    cred, unm = shape_credits('prov-p2k-20261110', 'PCQL')
    st = S('PCQL', 'prov-p2k-20261110', 'STATUS')
    # STATUS-named proved claims: emitted_not_compiled (DotFinish, DotPushLocal, NFS_AccumPart00) + externals PROVED_FRESH_EQ_GATE
    # (qm31_m31_dot -> RPu_FIq_Native02, selected_mask_value -> AspisR1SelectedMaskProbe, Prefix.payload -> AspisR1PrefixAggregateParser)
    # + m1b_files FinishCandidateExplicitOps (exit 0, 3 theorems; PCWN_STATUS later lists the same closure as settled).
    allowed = {'AspisR1CanonicalDotFinish.Funs', 'AspisR1DotPushLocal.Funs', 'NFS_AccumPart00', 'FinishCandidateExplicitOps',
               'RPu_FIq_Native02', 'AspisR1SelectedMaskProbe.Funs', 'AspisR1PrefixAggregateParser.Funs'}
    recs = []; notes = []
    for k, th in cred.items():
        if k.split('|')[0] in allowed:
            recs.append(assign('PCQL', k, 'EQUALITY_PROVED_JOB', 'PCQL STATUS proved (%s)' % th, shape=True))
        else:
            notes.append(dict(key=k, reason='shape credit in a module PCQL STATUS does not claim; not applied', theorem=th))
    notes.append('STATUS emitted_not_compiled proved_in_this_job=%d; FinishCandidateExplicitOps closure is in m1b_files (exit 0, 3 theorems) and is not in that count of 10; credited here, difference of 1 from a strict 10 recorded' % st['emitted_not_compiled_definitions']['proved_in_this_job'])
    notes.append('externals premise witnesses (C1_TAG, C2_TAG, slot_offset typecheck) are PREMISE_WITNESS, not equalities: no change; unmatched shape credits: %d' % len(unm))
    return recs, notes, dict(shape_credits=len(cred), applied_modules=sorted(allowed), unmatched_shape=len(unm))


def a_PCVX():
    cred, unm = shape_credits('prov-p3u-20261110', 'PCVX')
    recs = []; notes = []
    for k, th in cred.items():
        if k.split('|')[0] == 'AspisR1TerminalDecoder.Funs':   # STATUS claim C1: 87 definitions of this gate module
            recs.append(assign('PCVX', k, 'EQUALITY_PROVED_JOB', 'PCVX C1 fresh = gate (%s)' % th, shape=True))
        else:
            notes.append(dict(key=k, reason='outside STATUS claim C1', theorem=th))
    notes.append('C2/C3 (deployed op24/op21 slots vs frozen emission) relate deployed slots, not gate definitions: no key; stage-2/tx2 slot items are CANNOT_EXTRACT/EMITTED_NOT_RELATED: no change; C1 claims 87 definitions, %d resolve in the baseline universe, %d are UNMATCHED' % (len(recs), len(unm)))
    unmatched.extend(dict(job='PCVX', **u) for u in unm)
    return recs, notes, dict(status_claim_defs=87, resolved_in_baseline=len(recs), unmatched=len(unm))


def a_PCVZ():
    st = S('PCVZ', 'prov-p3w-20261110', 'STATUS')
    recs = []; notes = []
    for it in st['proved']:
        m = re.match(r'(.+?) \((.+)\)$', it['item']); name, mod = m.group(1), m.group(2)
        mod = mod.strip()
        k = resolve(mod, name)
        if not k:
            unmatched.append(dict(job='PCVZ', item=it['item'], reason='UNMATCHED: no unique baseline key')); continue
        if it['status'] == 'EQUALITY_PROVED': recs.append(assign('PCVZ', k, 'EQUALITY_PROVED_JOB', 'PCVZ ' + it['theorem']))
        elif it['status'] == 'LOOP_RETURN_REFINEMENT': recs.append(assign('PCVZ', k, 'REFINEMENT_LOOP_RETURN', 'PCVZ ' + it['theorem'], hm=['HM-B', 'HM-D']))
        else: unmatched.append(dict(job='PCVZ', item=it['item'], reason='unknown status ' + it['status']))
    hm_job_level.append(dict(job='PCVZ', text=st['library_model_dependency'],
                             note='job-level statement (HM-D Array.map gate model, HM-B IterMut.next); applied per definition to the two LOOP_RETURN_REFINEMENT records; the three EQUALITY_PROVED records keep their STATUS class and the lead should confirm that none of them uses the HM rows'))
    return recs, notes, dict(proved_items=len(st['proved']), mapped=len(recs))


def a_PCVY():
    return [], ['STATUS: op50 OPEN (unchanged); nothing credited'], dict(records=0)


def a_PCWF():
    st = S('PCWF', 'prov-p3x-20261110', 'STATUS')
    recs = []; notes = []
    it = st['items']
    q = 'AspisR1Qm31ArithmeticProbe.Funs'
    for n in it['B_covered_differs']['Qm31ArithmeticProbe_7']['definitions']:
        recs.append(assign('PCWF', resolve(q, n) or (q + '|?' + n), 'EQUALITY_PROVED_JOB', 'PCWF B Qm31 probe EQUALITY_PROVED (config ON)'))
    for n in it['C_callee_differs']['NGD_SlotRef_slot_offset_3']['definitions']:
        recs.append(assign('PCWF', 'NGD_SlotRef.Funs|' + n, 'OFF_EMISSION_WRAPPING_ACCEPTED', 'PCWF C slot_offset OFF emission; accepted by the Stream A lead as OFF_EMISSION_WRAPPING'))
    recs.append(assign('PCWF', 'AspisR72Sampler.Funs|AspisR72Sampler.field.r24_canonical_mul', 'EQUALITY_DOMAIN', 'PCWF A verdict EQUALITY_DOMAIN (all limbs < P); counts_as other'))
    recs.append(assign('PCWF', 'NCX_Reference.Types|NCX_Reference.VerifierRegistryEntryV2', 'TYPE_ISOMORPHISM', 'PCWF C verdict ISOMORPHISM; counts_as other'))
    recs.append(assign('PCWF', 'Op3I_Source|Op3I_Source.verifier.candidate.parse_shape', 'DEPENDS_ON_LIBRARY_TRUST', 'PCWF B verdict DEPENDS_ON_LIBRARY_TRUST', hm=['HM-B', 'HM-D']))
    notes.append('28 callee equalities of parse_shape (incl. Op3I_Source.transport.Variant.tag) are listed inside the DEPENDS item, not as per-key claims: not credited; Variant.tag stays at its baseline class')
    notes.append('NGD_SlotRef.OFF_NODES: STATUS says it settles the TEXT_DIFFERS record as a value equality but "not in the 12"; not credited')
    return recs, notes, dict(items=5, mapped=len(recs))


def a_PCXK():
    f = S('PCXK', 'prov-p6h-20261110', 'FAILED')
    wd = f['trust_row_withdrawn']['definitions']
    in_base = [d['key'] for d in wd if d['key'] in base]
    hb = [d for d in f['definitions'] if d.get('demote')]
    st = S('PCXK', 'prov-p6h-20261110', 'STATUS')
    return [], ['heartbeat demotions %d; trust_row_withdrawn keys %d of which %d in the baseline universe (STATUS: none in the cone); no class change' % (len(hb), len(wd), len(in_base))], dict(heartbeat_demotions=len(hb), withdrawn=len(wd), withdrawn_in_baseline=len(in_base), status_counts=st['counts'])


def a_PCWK():
    k = 'AspisV8R19.QuarticFieldSlice|AspisR66Field.field.r23_product_u32_bounded'
    recs = [assign('PCWK', k, 'GATE_ONLY_HELPER', 'PCWK C3 GATE_ONLY_HELPER, cleared only through its parents (gate CM31.mul/square), never SETTLED alone')]
    notes = ['M31.mul Guarded/Complex/Quartic EQUALITY_PROVED total: the three keys are already EQUALITY_PROVED at baseline (PCWK-C2): no change',
             'only the Quartic r23 key is proved (PRVEq.AspisV8R19.QuarticFieldSlice.field.r23_gate); AspisR72Sampler r23_product_u32_bounded stays NO_FROZEN_COUNTERPART']
    return recs, notes, dict(claims=2, mapped=1)


def a_PCWH():
    st = S('PCWH', 'prov-p4x-20261110', 'STATUS')
    cred, unm = shape_credits('prov-p4x-20261110', 'PCWH')
    unmatched.extend(dict(job='PCWH', **u) for u in unm)
    return [], ['public_bytes SETTLED (fresh = gate, PCWH_L003) sits in AspisR1PublicPreparation.Funs, outside the PCXH baseline universe (PCXK_FAILED lists the withdrawn row keys likewise): %d shape credits UNMATCHED, no count effect. The nine slice-iterator roots are NOT SETTLED/OPEN and are not baseline OPEN-class keys. Lead correction: node_count and semantic_value OPEN.' % len(unm)], dict(per_item=len(st['per_item']), unmatched_shape=len(unm))


def a_PCWJ():
    st = S('PCWJ', 'prov-p5a-20261110', 'STATUS')
    recs = []
    for r in st['settled_this_job']['records']:
        recs.append(assign('PCWJ', r['module'] + '|' + r['definition'], 'EQUALITY_PROVED_JOB', 'PCWJ ' + r['theorem']))
    for r in st['off_emission_wrapping']['records']:
        recs.append(assign('PCWJ', r['module'] + '|' + r['definition'], 'OFF_EMISSION_WRAPPING_ACCEPTED', 'PCWJ FIn_WeightsFuns OFF emission; accepted by the Stream A lead'))
    return recs, ['per-module causes (DEPENDS_ON_LIBRARY_TRUST from_fn, TYPES, NO_FROZEN_COUNTERPART, SOURCE_SHAPE) are causes of still-OPEN keys, not proved results (PCWH lead correction: DEPENDS_ON_LIBRARY_TRUST needs a proved fresh = gate): no change'], dict(settled=len(st['settled_this_job']['records']), off_emission=len(st['off_emission_wrapping']['records']))


# PCWM: Types-cause SETTLED records split by what the source proves (theorem `=` vs Equiv)
def pcwm_type_kinds(st):
    eqs = set(); equivs = set()
    for sc in ('L003', 'L004', 'L005', 'L006', 'L007', 'L008', 'L020', 'L021', 'L022', 'L023'):
        base_p = E + 'prov-p5d-20261110/PCWM_%s/sources/PCWM_sources/' % sc
        rc = subprocess.run(['git', 'ls-tree', '--name-only', REF, base_p], capture_output=True).stdout.decode().split()
        rcpt = tryshow(E + 'prov-p5d-20261110/PCWM_%s.json' % sc)
        if rcpt is None: continue
        try: ex = json.loads(rcpt).get('exit_status', json.loads(rcpt).get('exit'))
        except Exception: ex = None
        for p in rc:
            if 'Types_w' not in p: continue
            txt = show(p)
            for m in re.finditer(r'^theorem\s+PRVEq\.\S+?_(?:w\d)\.(\S+)\s*:\s*@\S+\s*=\s*@', txt, re.M): eqs.add(m.group(1))
            for m in re.finditer(r'^def\s+PRVEq\.\S+?_(?:w\d)\.(\S+)\.equiv\b', txt, re.M): equivs.add(m.group(1))
    return eqs, equivs


def a_PCWM():
    st = S('PCWM', 'prov-p5d-20261110', 'STATUS')
    eqs, equivs = pcwm_type_kinds(st)
    recs = []; notes = []; cnt = collections.Counter()
    for k, v in st['definitions'].items():
        s = v['status']; hm = None
        if s == 'SETTLED':
            if str(v.get('cause', '')).startswith('TYPES'):
                short = k.split('|', 1)[1].split('.', 1)[1]
                if short in eqs: new = 'EQUALITY_PROVED_JOB'
                elif short in equivs: new = 'TYPE_ISOMORPHISM'
                else:
                    unmatched.append(dict(job='PCWM', key=k, reason='SETTLED type with neither an `=` theorem nor an .equiv def found in the Types sources')); continue
            else: new = 'EQUALITY_PROVED_JOB'
        elif s == 'CONDITIONAL_ON_BINDING':
            new = 'CONDITIONAL_ON_BINDING'
            if 'HM-B' in (v.get('note') or ''): hm = ['HM-B', 'HM-D']
        elif s == 'OPEN_RECONSTRUCTED_SOURCE': new = 'OPEN_RECONSTRUCTED_SOURCE'
        elif s == 'OPEN': new = 'OPEN'
        else:
            unmatched.append(dict(job='PCWM', key=k, reason='unknown status ' + s)); continue
        cnt[new] += 1
        recs.append(assign('PCWM', k, new, 'PCWM STATUS ' + s, hm=hm))
    notes.append('lead_corrections applied: SETTLED_CONDITIONAL_ON_BINDING -> CONDITIONAL_ON_BINDING (other); S1ValuesOwnedModelV1 -> OPEN_RECONSTRUCTED_SOURCE (not settled)')
    notes.append('PCWM Types-cause SETTLED split by source: `@F = @G` theorems stay settled, Equiv (.equiv defs) become TYPE_ISOMORPHISM, the rule the lead applied to PCWL/PCWN')
    return recs, notes, dict(definitions=len(st['definitions']), by_class=dict(cnt))


def a_PCWL():
    st = S('PCWL', 'prov-p5c-20261110', 'STATUS')
    m = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB', 'TYPE_ISOMORPHISM': 'TYPE_ISOMORPHISM', 'CONDITIONAL_ON_BINDING': 'CONDITIONAL_ON_BINDING',
         'GATE_ONLY_HELPER_CLEARED_THROUGH_PARENT': 'GATE_ONLY_HELPER', 'OPEN': 'OPEN'}
    recs = []; cnt = collections.Counter()
    for x in st['definitions']:
        new = m[x['status']]; cnt[new] += 1
        recs.append(assign('PCWL', x['module'] + '|' + x['definition'], new, 'PCWL STATUS ' + x['status']))
    return recs, ['lead_correction applied: Equiv-proved records are TYPE_ISOMORPHISM (statuses already carry it)'], dict(definitions=len(st['definitions']), by_class=dict(cnt))


def a_generic_lead_classes(pre, d):
    st = S(pre, d, 'STATUS')
    lc = st['lead_classes']
    m = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB', 'TYPE_ISOMORPHISM': 'TYPE_ISOMORPHISM'}
    recs = []; cnt = collections.Counter()
    for k, v in lc.items():
        new = m.get(v, v); cnt[new] += 1
        recs.append(assign(pre, k, new, pre + ' lead_classes ' + v))
    notes = ['%s: items already in the target class from earlier jobs count as mapped but unchanged' % pre]
    return recs, notes, dict(lead_classes=len(lc), by_class=dict(cnt))


JOBS = [('p2k', 'PCQL', 'prov-p2k-20261110', a_PCQL), ('p3u', 'PCVX', 'prov-p3u-20261110', a_PCVX), ('p3w', 'PCVZ', 'prov-p3w-20261110', a_PCVZ),
        ('p3v', 'PCVY', 'prov-p3v-20261110', a_PCVY), ('p3x', 'PCWF', 'prov-p3x-20261110', a_PCWF), ('p6h', 'PCXK', 'prov-p6h-20261110', a_PCXK),
        ('p5b', 'PCWK', 'prov-p5b-20261110', a_PCWK), ('p4x', 'PCWH', 'prov-p4x-20261110', a_PCWH), ('p5a', 'PCWJ', 'prov-p5a-20261110', a_PCWJ),
        ('p5d', 'PCWM', 'prov-p5d-20261110', a_PCWM), ('p5c', 'PCWL', 'prov-p5c-20261110', a_PCWL),
        ('p5e', 'PCWN', 'prov-p5e-20261110', lambda: a_generic_lead_classes('PCWN', 'prov-p5e-20261110'))]
for spec in args.job:
    d, pre = spec.split(':')
    JOBS.append((d, pre, d, (lambda pre=pre, d=d: a_generic_lead_classes(pre, d))))

print('baseline %d/%d/%d rows %d' % (b0['settled'], b0['not_settled'], b0['other'], b0['rows_settled_only']))
for job, pre, d, fn in JOBS:
    run_job(job, pre, d, fn)
final = numbers(cls)

# ---------------------------------------------------------------- HM rows and listings
hm_base = []
for r in TRUST['records']:
    k = f"{r['module']}|{r['definition']}"
    if k in cone and base.get(k) == 'DEPENDS_ON_LIBRARY_TRUST':
        for t in r['trust_rows']:
            row = t.split(' ')[0]
            hm_rows[row].append(dict(key=k, job='baseline', class_='DEPENDS_ON_LIBRARY_TRUST', in_cone=True))
hm_listing = {h: sorted({(x['key'], x['job'], x['class_']) for x in v}) for h, v in hm_rows.items()}
by_class = collections.defaultdict(list)
for k in sorted(cone): by_class[cls[k]].append(k)
settled_with_trust = sorted(k for k in cone if cls[k] in SET and any(k == f"{r['module']}|{r['definition']}" for r in TRUST['records']))

# ---------------------------------------------------------------- comparison with the lead's hand counts (reported, never tuned to)
HAND = {'PCXK': (1096, 542, 69), 'PCWJ': (1122, 516, 69), 'PCWM': (1125, 494, 88), 'PCWL': (1131, 460, 116), 'PCWN': (1142, 441, 124)}
hand_cmp = {}
for j in log:
    if j['prefix'] in HAND:
        a = j['after']; h = HAND[j['prefix']]
        hand_cmp[j['prefix']] = dict(lead=dict(settled=h[0], not_settled=h[1], other=h[2]), mine=dict(settled=a['settled'], not_settled=a['not_settled'], other=a['other']),
                                     diff=dict(settled=a['settled'] - h[0], not_settled=a['not_settled'] - h[1], other=a['other'] - h[2]), rows_settled_only=a['rows_settled_only'], lead_rows=120)
wc = sorted(k for k in J(E + 'prov-p5d-20261110/PCWM_STATUS.json')['definitions'] if k.startswith('AspisR1WithdrawalCaller.Funs|'))
pcwn = next(j for j in log if j['prefix'] == 'PCWN')
lc_all = J(E + 'prov-p5e-20261110/PCWN_STATUS.json')['lead_classes']
already = sorted(k for k in lc_all if k in cone and cls[k] in SET and k not in {c['key'] for c in pcwn['change_list']})
not_cone = sorted(k for k in lc_all if k not in cone)
attrib = {
    'PCWK_r23': dict(keys=['AspisV8R19.QuarticFieldSlice|AspisR66Field.field.r23_product_u32_bounded'], effect='mine: GATE_ONLY_HELPER (other) from p5b; lead hand counts did not move it (not settled -> other, 1 key)'),
    'PCWM_WithdrawalCaller_8': dict(keys=wc, effect='mine: 5 EQUALITY_PROVED (SETTLED in STATUS) + 3 CONDITIONAL_ON_BINDING from p5d; lead p5d delta (+3 settled, +19 other) covers only the 3 type equalities, 12 Equiv types and the 7 Qm31SamplerIndex conditionals'),
    'PCWN_already_settled_before_p5e': dict(keys=already, effect='lead_classes EQUALITY_PROVED keys that earlier jobs already settled (PCQL DotFinish P/reduce/Q.limbs, FinishCandidateExplicitOps closure): no new settled in this chain; the lead hand delta of +11 counts them'),
    'PCWN_lead_class_keys_outside_cone': dict(keys=not_cone, effect='in PCWN lead_classes but not in the 1707 cone: classified, no count effect here'),
}
prev = b0; deltas = []
for j in log:
    a = j['after']
    deltas.append(dict(job=j['job'], prefix=j['prefix'], settled=a['settled'], not_settled=a['not_settled'], other=a['other'], rows_settled_only=a['rows_settled_only'], **{'delta_' + k: v for k, v in j['delta'].items()}))
out = dict(schema='PCXL_COUNTS/1', target_established=False, ref=REF, baseline=b0, jobs=[{k: v for k, v in j.items() if k != 'change_list'} for j in log],
           per_job_numbers=deltas, lead_hand_comparison=hand_cmp, difference_attribution=attrib, final=final,
           headline=dict(settled_of_1707=final['settled'], not_settled_of_1707=final['not_settled'], other_of_1707=final['other'], rows_settled_only_of_599=final['rows_settled_only']),
           changes=[dict(job=j['prefix'], **c) for j in log for c in j['change_list']],
           unmatched=unmatched, conflicts=conflicts,
           per_class_lists={c: v for c, v in sorted(by_class.items())},
           per_hm_row_lists={h: [dict(key=a, job=b, class_=c) for a, b, c in v] for h, v in sorted(hm_listing.items())}, hm_job_level_statements=hm_job_level,
           settled_keys_that_also_appear_in_PCXF_TRUST_NAMING_records=settled_with_trust,
           fielderives_note='no job STATUS in this chain records a FieldDerives use per key; none listed (ReviewedTranscription-FieldDerives untouched by PCXK)')
if args.out:
    json.dump(out, open(args.out, 'w'), indent=1); open(args.out, 'a').write('\n')
    json.dump(dict(final_class=cls), open(args.out.replace('.json', '_CLASSES.json'), 'w'))
print('FINAL settled %d not settled %d other %d | rows settled-only %d of 599 | unmatched %d conflicts %d' % (final['settled'], final['not_settled'], final['other'], final['rows_settled_only'], len(unmatched), len(conflicts)))


def rows_settled_only_if(keys, classes=None):
    """Rows (of 599) that are settled-only if every cone key in `keys` were SETTLED and nothing else changed.
    `classes` defaults to the final class map of this recount. Returns dict(rows_settled_only=int, rows=[row names], baseline_rows=int)."""
    c = dict(classes if classes is not None else cls)
    for k in keys:
        if k not in cone: raise KeyError('not a cone key: ' + k)
        c[k] = 'EQUALITY_PROVED_JOB'
    rs = row_status(c)
    rows = sorted(r for r, t in rs.items() if t['N'] == 0 and t['O'] == 0 and t['U'] == 0 and t['S'] > 0)
    return dict(rows_settled_only=len(rows), rows=rows, baseline_rows=numbers(classes if classes is not None else cls)['rows_settled_only'])


if args.assume_settled:
    print(json.dumps({k: v for k, v in rows_settled_only_if(json.load(open(args.assume_settled))).items() if k != 'rows'}))
