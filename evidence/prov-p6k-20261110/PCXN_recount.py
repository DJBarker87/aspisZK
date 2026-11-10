#!/usr/bin/env python3
"""PCXN_recount.py (P6k): PCXL_recount.py (P6i, copied unchanged up to the chain) extended with the Stream A lead overlays of 2026-11-10.
The PCXL docstring follows.

PCXL_recount.py: headline recount by each job's STATUS CLASSES (not theorem shape).

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
ap.add_argument('--out', default=None, help='(PCXL option, unused by PCXN) ')
ap.add_argument('--outdir', default='evidence/prov-p6k-20261110', help='PCXN outputs are written here (run from the worktree root)')
ap.add_argument('--assume-settled', default=None, help='JSON list of cone keys treated as SETTLED; prints rows settled-only of 599')
args = ap.parse_args() if __name__ == '__main__' else ap.parse_args([])
REF = subprocess.run(['git', 'rev-parse', args.ref], capture_output=True, check=True).stdout.decode().strip()   # pinned to one commit so every read is consistent
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


def a_PCWG():
    st = S('PCWG', 'prov-p3y-20261110', 'STATUS')
    recs = []; notes = []; cnt = collections.Counter()
    for x in st['items']:
        d = x['definition']; lc = x['lead_class'].split(' ')[0]
        cands = byname.get(d, [])
        if len(cands) > 1:
            pref = [c for c in cands if c.endswith('.Funs')]
            cands = pref if len(pref) == 1 else cands
        if len(cands) != 1:
            unmatched.append(dict(job='PCWG', definition=d, modules=cands, reason='UNMATCHED/AMBIGUOUS gate module')); continue
        k = cands[0] + '|' + d
        new = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB', 'OPEN': 'OPEN'}.get(lc, lc)
        hm = None
        if lc == 'DEPENDS_ON_LIBRARY_TRUST':
            hm = sorted(set(re.findall(r'HM-[A-G]', json.dumps(x)))) or None
            if not hm: hm_job_level.append(dict(job='PCWG', key=k, text='DEPENDS_ON_LIBRARY_TRUST without a named HM row in the STATUS item'))
        cnt[new] += 1
        before = cls.get(k)
        r = assign('PCWG', k, new, 'PCWG lead_class ' + x['lead_class'], hm=hm)
        if r and k == 'NGD_SlotRef.Funs|NGD_SlotRef.OFF_NODES':
            notes.append('OFF_NODES: class before P3y = %s; PCWF (P3x) did not credit it (its STATUS says "not in the 12"), so there is no double credit; now %s' % (before, cls[k]))
        recs.append(r)
    notes.append('only lead_class EQUALITY_PROVED counts as settled; others other/open per the STATUS lead_corrections; STATUS "SETTLED" for loop-return and type-map refinements is NOT credited')
    return recs, notes, dict(items=len(st['items']), mapped=len(recs), by_class=dict(cnt))


JOBS = [('p2k', 'PCQL', 'prov-p2k-20261110', a_PCQL), ('p3u', 'PCVX', 'prov-p3u-20261110', a_PCVX), ('p3w', 'PCVZ', 'prov-p3w-20261110', a_PCVZ),
        ('p3v', 'PCVY', 'prov-p3v-20261110', a_PCVY), ('p3x', 'PCWF', 'prov-p3x-20261110', a_PCWF), ('p6h', 'PCXK', 'prov-p6h-20261110', a_PCXK),
        ('p5b', 'PCWK', 'prov-p5b-20261110', a_PCWK), ('p4x', 'PCWH', 'prov-p4x-20261110', a_PCWH), ('p5a', 'PCWJ', 'prov-p5a-20261110', a_PCWJ),
        ('p5d', 'PCWM', 'prov-p5d-20261110', a_PCWM), ('p5c', 'PCWL', 'prov-p5c-20261110', a_PCWL),
        ('p5e', 'PCWN', 'prov-p5e-20261110', lambda: a_generic_lead_classes('PCWN', 'prov-p5e-20261110')),
        ('p3y', 'PCWG', 'prov-p3y-20261110', a_PCWG)]
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
HAND = {'PCXK': (1096, 542, 69), 'PCWJ': (1122, 516, 69), 'PCWM': (1125, 494, 88), 'PCWL': (1131, 460, 116), 'PCWN': (1142, 441, 124)}  # P3y has no hand count yet
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


# =====================================================================================================================
# PCXN additions (P6k). Everything above this line is PCXL_recount.py (P6i); the chain it runs is reproduced first.
# =====================================================================================================================
import os, lzma  # noqa

if __name__ == '__main__' or True:
    OUT = args.outdir

    # ---------------------------------------------------------------- 0. reproduction of PCXL's final numbers
    REPRO = dict(settled=final['settled'], not_settled=final['not_settled'], other=final['other'], rows_settled_only=final['rows_settled_only'])
    assert (REPRO['settled'], REPRO['not_settled'], REPRO['other'], REPRO['rows_settled_only']) == (1150, 420, 137, 122), ('PCXL final not reproduced', REPRO)
    print('PCXN reproduction of PCXL final: %(settled)d/%(not_settled)d/%(other)d rows %(rows_settled_only)d  OK' % REPRO)

    # merged jobs after d80d89716a0 on research: adapters needed only for evidence/prov-p*-20261110 jobs other than the already-chained ones
    r = subprocess.run(['git', 'log', REF, '--name-only', '--format=%H %s', 'd80d89716a0..' + REF], capture_output=True, check=True).stdout.decode()
    new_dirs = sorted({m.group(0) for m in re.finditer(r'evidence/prov-p[0-9a-z]+-2026111?\d', r)})
    chained = {j[2] for j in JOBS}
    unchained = [d for d in new_dirs if d.split('/')[1] not in chained]
    research_head = subprocess.run(['git', 'rev-parse', REF], capture_output=True).stdout.decode().strip()
    print('research head', research_head[:12], 'evidence dirs touched after d80d89716a0:', new_dirs, 'unchained:', unchained)
    assert unchained == ['evidence/prov-p5f-20261110', 'evidence/prov-p5h-20261110', 'evidence/prov-p6j-20261110'], unchained   # P5f (PCWP_), P5h (PCWR_) get adapters below; P6j (PCXM_) is exposure only: no class map, no STATUS
    MERGED_AFTER_D80 = dict(research_head=research_head, evidence_dirs_after_d80d89716a0=new_dirs,
                            conclusion='three evidence dirs: prov-p5f-20261110 (PCWP_) and prov-p5h-20261110 (PCWR_), both merged after d80d89716a0 (adapters a_PCWP, a_PCWR added, applied in merge order after overlay O1 and before O2), and prov-p6j-20261110 (PCXM_ exposure table, no per-key class map, no STATUS file: no adapter)')

    def snap():
        return numbers(cls)

    def brief(n):
        return dict(settled=n['settled'], not_settled=n['not_settled'], other=n['other'], rows_settled_only=n['rows_settled_only'],
                    settled_classes=n['settled_classes'], not_settled_classes=n['not_settled_classes'], other_classes=n['other_classes'])

    n0 = snap()
    overlays = []

    # ---------------------------------------------------------------- 1. overlay (1): HAND_ADAPTED and NO_FROZEN_COUNTERPART are NOT SETTLED
    NOTSET |= {'HAND_ADAPTED', 'NO_FROZEN_COUNTERPART'}
    n1 = snap()
    moved1 = sorted(k for k in cone if cls[k] in ('HAND_ADAPTED', 'NO_FROZEN_COUNTERPART'))
    assert (n1['settled'], n1['not_settled'], n1['other']) == (1150, 428, 129), n1
    overlays.append(dict(name='O1 HAND_ADAPTED(5) + NO_FROZEN_COUNTERPART(3) count NOT SETTLED (decision 1)', before=brief(n0), after=brief(n1),
                         delta=dict(settled=n1['settled'] - n0['settled'], not_settled=n1['not_settled'] - n0['not_settled'], other=n1['other'] - n0['other'], rows_settled_only=n1['rows_settled_only'] - n0['rows_settled_only']),
                         keys=[dict(key=k, class_=cls[k], in_cone=True) for k in moved1],
                         note='class labels unchanged; the two classes move from the OTHER bucket to NOT SETTLED. 1 further NO_FROZEN_COUNTERPART key of the 1876-key universe is outside the 1707 cone (not counted).'))
    print('O1 ->', n1['settled'], n1['not_settled'], n1['other'], 'rows', n1['rows_settled_only'])

    # ---------------------------------------------------------------- 1b. P5f (PCWP_) merged after d80d89716a0: adapter
    def a_PCWP():
        st = S('PCWP', 'prov-p5f-20261110', 'STATUS')
        m = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB'}
        recs = []; cnt = collections.Counter()
        for x in st['records']:
            new = m.get(x['cls'], x['cls']); cnt[new] += 1
            hm = x['rows'] if x['cls'] == 'DEPENDS_ON_LIBRARY_TRUST' else None
            recs.append(assign('PCWP', x['module'] + '|' + x['definition'], new, 'PCWP STATUS ' + x['cls'] + ' (' + x['scope'] + ')', hm=hm))
        notes = ['STATUS classification_rule already applies the lead ruling (any definition proved through from_fn HM-D is DEPENDS_ON_LIBRARY_TRUST, never SETTLED); no lead_corrections key in this STATUS',
                 'item1 lemma (from_fn gate-model semantics, PCWP_L002) is a lemma about the gate model, not a key credit']
        return recs, notes, dict(records=len(st['records']), by_class=dict(cnt))
    nb = snap()
    run_job('p5f', 'PCWP', 'prov-p5f-20261110', a_PCWP)
    n1b = snap()
    pcwp_changes = log[-1]['change_list']
    overlays.append(dict(name='P5f (PCWP_) job adapter, merged on research after d80d89716a0', before=brief(nb), after=brief(n1b),
                         delta=dict(settled=n1b['settled'] - nb['settled'], not_settled=n1b['not_settled'] - nb['not_settled'], other=n1b['other'] - nb['other'], rows_settled_only=n1b['rows_settled_only'] - nb['rows_settled_only']),
                         keys=[dict(key=c['key'], was=c['was'], now=c['now'], in_cone=c['in_cone']) for c in pcwp_changes]))
    n1 = n1b

    # ---------------------------------------------------------------- 1c. P5h (PCWR_) merged after P5f: adapter
    def a_PCWR():
        st = S('PCWR', 'prov-p5h-20261110', 'STATUS')
        recs = []; cnt = collections.Counter()
        for k, v in st['definitions'].items():
            new = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB'}.get(v['status'], v['status']); cnt[new] += 1
            recs.append(assign('PCWR', k, new, 'PCWR STATUS ' + v['status'] + ' (' + str(v.get('scope')) + ')'))
        notes = ['Qm31SamplerIndex 7 keys: unconditional fresh = gate, supersede the PCWM CONDITIONAL_ON_BINDING (recorded as a conflict rule other -> settled: strongest proved class wins)',
                 'S1ValuesOwnedModelV1: 5 GATE_ONLY_HELPER (other) replace OPEN_RECONSTRUCTED_SOURCE for 5 keys, 3 stay OPEN (STATUS classes applied as given)',
                 'S8OwnedP6 8 OPEN and OraclePort 8 OPEN (STATUS; OraclePort text says NO_FROZEN_COUNTERPART): baseline other-class keys keep their class by the PCXL rule (an open label never weakens an already classed other-class key); not-settled either way after O1',
                 'item1 (source-sha audit, AdapterRwModel re-pointed to lean-040) is a citation fix: no class change']
        return recs, notes, dict(definitions=len(st['definitions']), by_class=dict(cnt))
    nb = snap()
    run_job('p5h', 'PCWR', 'prov-p5h-20261110', a_PCWR)
    n1c = snap()
    overlays.append(dict(name='P5h (PCWR_) job adapter, merged on research after d80d89716a0 (after P5f)', before=brief(nb), after=brief(n1c),
                         delta=dict(settled=n1c['settled'] - nb['settled'], not_settled=n1c['not_settled'] - nb['not_settled'], other=n1c['other'] - nb['other'], rows_settled_only=n1c['rows_settled_only'] - nb['rows_settled_only']),
                         keys=[dict(key=c['key'], was=c['was'], now=c['now'], in_cone=c['in_cone']) for c in log[-1]['change_list']]))
    n1 = n1c

    # ---------------------------------------------------------------- 2. overlay (2): retroactive owner rule, OPEN_TRANSCRIPTION
    PCXM = J(E + 'prov-p6j-20261110/PCXM_EXPOSURE.json')
    items = [it for it in PCXM['table1'] if it.get('subject') == 'ASPIS_CODE']
    assert len(items) == 51 and sum(1 for it in items if it['discharge'] != 'DISCHARGED_BY_KEYS') == 50
    NOTSET.add('OPEN_TRANSCRIPTION')
    FRESH_GATE = {'EQUALITY_PROVED', 'EQUALITY_PROVED_P1N', 'EQUALITY_PROVED_JOB', 'OFF_EMISSION_WRAPPING_ACCEPTED'}
    CREDIT_NOT_FRESH = {'RECEIPTED_PIN_EQUAL', 'RECEIPTED_SELECTED_MASK_PROBE'}     # settled classes that are not a fresh = gate theorem
    assert SET == FRESH_GATE | CREDIT_NOT_FRESH, SET
    k2items = collections.defaultdict(list)
    for it in items:
        for k in set(it['fn_keys_in_cone']) | set(it['specific_keys']):
            k2items[k].append(it['item'])
    reclass = []
    for k in sorted(k2items):
        if k in cone and cls[k] in CREDIT_NOT_FRESH:
            reclass.append(dict(key=k, was=cls[k], now='OPEN_TRANSCRIPTION', items=sorted(k2items[k])))
    for x in reclass:
        cls[x['key']] = 'OPEN_TRANSCRIPTION'
    n2 = snap()
    item_records = []
    for it in items:
        mk = sorted(set(it['fn_keys_in_cone']) | set(it['specific_keys']))
        item_records.append(dict(item=it['item'], status='OPEN_TRANSCRIPTION', was_discharged_by_keys=(it['discharge'] == 'DISCHARGED_BY_KEYS'),
                                 note=('NKM-RTNGB006: no longer discharged; its one function key is EQUALITY_PROVED by a fresh = gate proof and keeps that class; no item-specific theorem is cited'
                                       if it['discharge'] == 'DISCHARGED_BY_KEYS' else None),
                                 rows=it['rows'], functions=it['functions'], function_keys=it['fn_keys_in_cone'], item_specific_keys=it['specific_keys'],
                                 mapped_key_classes_after=dict(collections.Counter(cls[k] for k in mk)),
                                 reclassified_keys=[x['key'] for x in reclass if it['item'] in x['items']],
                                 unmapped=(len(mk) == 0), ce=bool(it.get('ce'))))
    unmapped_items = [x['item'] for x in item_records if x['unmapped']]
    overlays.append(dict(name='O2 retroactive owner rule: 51 Aspis-code ReviewedTranscription items OPEN_TRANSCRIPTION; credit-through-RT keys reclassified (decision 2)',
                         before=brief(n1), after=brief(n2),
                         delta=dict(settled=n2['settled'] - n1['settled'], not_settled=n2['not_settled'] - n1['not_settled'], other=n2['other'] - n1['other'], rows_settled_only=n2['rows_settled_only'] - n1['rows_settled_only']),
                         keys=reclass,
                         rule='a cone key moves to OPEN_TRANSCRIPTION iff (a) it is a function key or item-specific key of one of the 51 Aspis-code items in PCXM_EXPOSURE table1 (fn_keys_in_cone, specific_keys) and (b) its current class is a settled class that is not a fresh = gate proof (RECEIPTED_PIN_EQUAL, RECEIPTED_SELECTED_MASK_PROBE). Keys with a fresh = gate class (EQUALITY_PROVED, _P1N, _JOB, OFF_EMISSION_WRAPPING_ACCEPTED) keep it; keys already not settled or other keep their class.',
                         items_total=len(items), items_unmapped=len(unmapped_items)))
    print('O2 ->', n2['settled'], n2['not_settled'], n2['other'], 'rows', n2['rows_settled_only'], 'reclassified keys', len(reclass), 'unmapped items', len(unmapped_items))

    # sensitivity: every settled-by-receipt key of the items' own ledger rows (upper bound, PCXM's 557-key mapping not used for the headline)
    ub = set()
    for it in items:
        for rw in it['own_rows_in_599']:
            ub |= {k for k in rowdefs.get(rw, []) if k in cone}
    sens_ub = sorted(k for k in ub if k in cone and base.get(k) in CREDIT_NOT_FRESH and cls[k] not in ('OPEN_TRANSCRIPTION',) and cls[k] in CREDIT_NOT_FRESH)

    # ---------------------------------------------------------------- 3. CANNOT_EXTRACT consolidated table
    T2 = {t['item']: t for t in PCXM['table2']}
    T2keys = lambda lab: [k for k in T2[lab]['keys_in_cone']]
    def txt(path, sub, field=('error', 'errors', 'new_error', 'scopes', 'scope', 'tool_route', 'patch_effect', 'builds', 'routing', 'evidence', 'next')):
        d = J(E + path)
        for it in d['items']:
            if sub in it['item']:
                return {k: it[k] for k in field if k in it}
        raise KeyError((path, sub))
    def line(path, n):
        return show(E + path).splitlines()[n - 1]
    WH, WO, VX, VV = 'prov-p4x-20261110/PCWH_CANNOT_EXTRACT.json', 'prov-p4y-20261110/PCWO_CANNOT_EXTRACT.json', 'prov-p3u-20261110/PCVX_CANNOT_EXTRACT.json', 'prov-p3t-20261110/PCVV_CANNOT_EXTRACT.json'
    TOOL = dict(
        PCWH='second tool version: Charon 454586e9 + Aeneas 0d21a9ec (main HEAD 2026-11-09; binary_sha256 230ee9f0..., PCWH_TOOLS.json)',
        PCWO='third tool version: fork of Aeneas 0d21a9ec + PCWO patches A,B (aeneas sha256 6652776a..., PCWO_TOOLS.json), Charon 454586e9',
        PCVX='original Aeneas 959659a6 and extended Aeneas b59d5188 (PCVX_CANNOT_EXTRACT.json scopes)',
        PCVV='original Aeneas 959659a6 and extended Aeneas b59d5188 (PCVV_CANNOT_EXTRACT.json builds)',
        PCWL='original Aeneas 959659a6 (E001, E006) and extended Aeneas b59d5188 (E002-E004) (PCWL_HANDOFF.md line 18)',
        PCWM='original Aeneas 959659a6 and extended Aeneas b59d5188 (PCWM_E004/E005/E006, PCWM_STATUS.json definition notes)',
        PCWN='per PCWL/PCWH E008/E010 (no new extraction scope; PCWN_STATUS cargo_jobs: not applicable)',
        NJN='extended Aeneas b59d5188, aeneas_sha256 c0cf4fcc..., charon_sha256 daad69be... (NJN_EXTRACTION_PINS.json)',
        NMV='Aeneas aeneas_sha256 c0cf4fcc... (same binary as NJN), charon_sha256 daad69be..., toolchain nightly-2026-09-17 (NMV_E003/NMV_FISSION_EXTRACTION_PINS.json)')
    ev = lambda *a: [('evidence/' + x) for x in a]

    def wm_note(short):
        st = J(E + 'prov-p5d-20261110/PCWM_STATUS.json')['definitions']
        k = [k for k in st if k.endswith(short)][0]
        return st[k]['note']

    def pcwl_reason(modsub, defsub):
        st = J(E + 'prov-p5c-20261110/PCWL_STATUS.json')['definitions']
        for x in st:
            if modsub in x['module'] and x['definition'].endswith(defsub):
                return x['reason']
        raise KeyError((modsub, defsub))

    ARROW = txt(WH, 'tx2_authenticated')
    ARROW_VX = txt(VX, 'candidate::query_loop')
    CE_ITEMS = [
        dict(id='CE01', function='programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release (op50)', t2='op50 decode_lane_from_pool_release', rows_own=['TX2:217'],
             failures=[dict(job='PCWH', tool=TOOL['PCWH'], **txt(WH, 'decode_lane_from_pool_release')),
                       dict(job='PCVV', tool=TOOL['PCVV'], **txt(VV, 'decode_lane_from_pool_release')),
                       dict(job='PCWO', tool=TOOL['PCWO'], **txt(WO, 'op50'))],
             evidence=ev(WH, WO, VV)),
        dict(id='CE02', function='crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place', t2='verify_in_place', rows_own=[],
             failures=[dict(job='PCWH', tool=TOOL['PCWH'], **txt(WH, 'verify_in_place')), dict(job='PCVX', tool=TOOL['PCVX'], **txt(VX, 'verify_in_place'))], evidence=ev(WH, VX)),
        dict(id='CE03', function='crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim and Prepared::new', t2='Prepared::new / prepared_claim', rows_own=[],
             extra_groups=[('CurrentClaimDotModel six (PCWN: gate-only decompositions of prepared_claim)', T2keys('CurrentClaimDotModel six (prepared_claim, _dot, _dot_loop, _dot_loop.body, _loop, _loop.body)')),
                           ('PCWL CurrentClaimSumModel prepared_claim_sum, _loop, _loop.body (CANNOT_EXTRACT cause)', 'PCWL_CCS'),
                           ('PCWL S1ClaimBorrowedAbiNativeV1 + S1ClaimOwnedNestedModelV1 owned_* gate copies (cause CANNOT_EXTRACT / NO_FROZEN_COUNTERPART; frozen counterpart is prepared_claim)', 'PCWL_S1')],
             failures=[dict(job='PCWH', tool=TOOL['PCWH'], **txt(WH, 'Prepared::new')), dict(job='PCVX', tool=TOOL['PCVX'], **txt(VX, 'verifier::Prepared::new')),
                       dict(job='PCWL', tool=TOOL['PCWL'], error=line('prov-p5c-20261110/PCWL_HANDOFF.md', 18)), dict(job='PCWN', tool=TOOL['PCWN'], error=line('prov-p5e-20261110/PCWN_HANDOFF.md', 23))],
             evidence=ev(WH, VX, 'prov-p5c-20261110/PCWL_HANDOFF.md', 'prov-p5c-20261110/PCWL_STATUS.json', 'prov-p5e-20261110/PCWN_HANDOFF.md')),
        dict(id='CE04', function='crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord::decode_k', t2='decode_k', rows_own=[],
             failures=[dict(job='PCWH', tool=TOOL['PCWH'], **txt(WH, 'decode_k')), dict(job='PCWO', tool=TOOL['PCWO'], error='decode_k (r1_wire.rs 158-165) pulled in by the closure fails with the same join error (PCWO_E002: ' + txt(WO, 'semantic_boundary')['new_error'] + ')')], evidence=ev(WH, WO)),
    ]
    for fn, lab, fnsrc in (('candidate.rs::tx2_authenticated', 'tx2_authenticated', 'tx2_authenticated'), ('candidate.rs::tx2_common', 'tx2_common', 'tx2_authenticated'),
                           ('verifier.rs::mark', 'mark', 'tx2_authenticated'), ('candidate.rs::query_loop (op6)', 'query_loop (op6)', 'tx2_authenticated'),
                           ('candidate.rs::query_values', 'query_values', 'tx2_authenticated'), ('verifier.rs::finish_relation (op19)', 'finish_relation (op19)', 'tx2_authenticated')):
        CE_ITEMS.append(dict(id='CE%02d' % (len(CE_ITEMS) + 1), function='crates/aspis-r1-cost-probe/src/' + fn, t2=lab, rows_own=[],
                             failures=[dict(job='PCWH', tool=TOOL['PCWH'], note='one record for tx2_authenticated, tx2_common, mark, query_loop, query_values, finish_relation', **ARROW),
                                       dict(job='PCVX', tool=TOOL['PCVX'], **(txt(VX, 'verifier::finish_relation') if lab.startswith('finish') else ARROW_VX))], evidence=ev(WH, VX)))
    SB = txt(WH, 'r1_semantic::semantic_boundary')
    for fn, lab in (('r1_semantic.rs::semantic_boundary', 'semantic_boundary'), ('candidate_claims.rs::claims', 'claims'), ('r1_semantic.rs::semantic_rounds', 'semantic_rounds')):
        CE_ITEMS.append(dict(id='CE%02d' % (len(CE_ITEMS) + 1), function='crates/aspis-r1-cost-probe/src/' + fn, t2=lab, rows_own=[],
                             extra_groups=([('AspisR1SemanticCallExtraction eight (PCWM cause CANNOT_EXTRACT)', T2keys('AspisR1SemanticCallExtraction eight (semantic_boundary, semantic_value, _entry, _loop, _loop.body ...)'))] if lab == 'semantic_boundary' else []),
                             failures=[dict(job='PCWH', tool=TOOL['PCWH'], note='one record for the three functions', **SB), dict(job='PCWO', tool=TOOL['PCWO'], note='one record for the three functions', **txt(WO, 'semantic_boundary'))]
                             + ([dict(job='PCWM', tool=TOOL['PCWM'], error=wm_note('r1_semantic.semantic_boundary'))] if lab == 'semantic_boundary' else []),
                             evidence=ev(WH, WO) + (['evidence/prov-p5d-20261110/PCWM_STATUS.json'] if lab == 'semantic_boundary' else [])))
    CE_ITEMS += [
        dict(id='CE%02d' % (len(CE_ITEMS) + 1), function='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts', t2='require_distinct_accounts', rows_own=[],
             failures=[dict(job='PCWL', tool=TOOL['PCWL'], error=pcwl_reason('AdapterRwModel', 'require_distinct_accounts'))], evidence=ev('prov-p5c-20261110/PCWL_STATUS.json', 'prov-p5c-20261110/PCWL_HANDOFF.md')),
        dict(id='CE%02d' % (len(CE_ITEMS) + 2), function='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1 (op48) and ::decode_pool_v1_pair_forest_checkpoint_v1 (op49)',
             t2='raw decoders op48/op49 (decode_pool_v1_pair_forest_master_v1 / checkpoint_v1)', rows_own=[],
             failures=[dict(job='PCVX', tool=TOOL['PCVX'], **txt(VX, 'decode_pool_v1_pair_forest_master_v1')), dict(job='PCVX', tool=TOOL['PCVX'], **txt(VX, 'decode_pool_v1_pair_forest_checkpoint_v1'))], evidence=ev(VX)),
        dict(id='CE%02d' % (len(CE_ITEMS) + 3), function='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 (op22)',
             t2='op22 encode_pool_v1_pair_forest_terminal_statement_v1', rows_own=[],
             failures=[dict(job='PCVX', tool=TOOL['PCVX'], **txt(VX, 'encode_pool_v1_pair_forest_terminal_statement_v1'))], evidence=ev(VX)),
        dict(id='CE%02d' % (len(CE_ITEMS) + 4), function='crates/aspis-statement decoders as one closure (decode_pool_v1_pair_forest_terminal_statement_v1, boxed decoders, decode_pool_v1_pair_verified_afterstate_v1)',
             t2='other aspis_statement raw decoders (decode_pool_v1* name match)', rows_own=[], category='TIMEOUT (no error text; not a construct error)',
             failures=[dict(job='PCVX', tool=TOOL['PCVX'], **txt(VX, 'aspis_statement decoders as one closure'))], evidence=ev(VX),
             note='cone keys are a name match (decode_pool_v1*), mechanical, as in PCXM Table 2'),
        dict(id='CE%02d' % (len(CE_ITEMS) + 5), function='programs/r1-cost-probe/src/deployment_ids.rs::deployment_id (HM-A member, feeds op45, AUDIT_POOL_PROGRAM)', t2=None, rows_own=[],
             failures=[dict(job='PCVV', tool=TOOL['PCVV'], **txt(VV, 'deployment_ids::deployment_id'))], evidence=ev(VV),
             note='no cone key found by name matching (UNMAPPED); excluded from the owner-rule items as an HM-A SDK member by PCXM'),
        dict(id='CE%02d' % (len(CE_ITEMS) + 6), function='crates/aspis-statement validate_pool_v1_pair_forest_terminal_statement_v1 and encode_pool_v1_pair_verified_afterstate_v1 (stage1 op21, op24)', t2=None, rows_own=[],
             category='EXTRACTION_SHAPE_MISS (worker input defect, not a tool limitation)',
             failures=[dict(job='PCVV', tool=TOOL['PCVV'], **txt(VV, 'validate_pool_v1_pair_forest_terminal_statement_v1'))], evidence=ev(VV),
             note='listed because no emission exists; a later job (PCVX_E012) emitted the aspis_statement closure, so this is NOT a tool-level CANNOT_EXTRACT and contributes no key to the CE set'),
    ]
    # stage1 / stage2 adapter items (lead instruction)
    NJN_L001 = line('entry-sdk-20261108/NJN_FAILING_STEP.md', 5) + ' ' + line('entry-sdk-20261108/NJN_FAILING_STEP.md', 6)
    for sid, fn, row in (('stage1', 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1', 'TX1:344'), ('stage2', 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2', 'TX2:240')):
        CE_ITEMS.append(dict(id='CE%02d' % (len(CE_ITEMS) + 1), function=fn, t2=None, rows_own=[row], category='stage adapter (guard-holding SDK wrapper; ReviewedTranscription-%s via ruling (bn))' % row,
                             failures=[dict(job='NJN (entry-sdk)', tool=TOOL['NJN'], error='Aeneas exit 2 at InterpBorrows.ml:2731 on the guard drop\'s same-cell counter branch (NJN_reference.rs line 23); Charon exit 0; all twelve roots in one extraction; no Lean output. NJN_FAILING_STEP.md L001, verbatim: ' + ' '.join(NJN_L001.split()),
                                            scope='NJN_L001 (evidence/entry-sdk-20261108/NJN_FAILING_STEP.md L001)',
                                            note='that scope extracted NJN_reference.rs (the SDK Ref/RefMut guard reference, twelve roots), not the frozen stage wrapper itself; C3-BIN (be)(2) and (bn)(1) record that the same guard-drop class blocks the two stage bodies'),
                                       dict(job='NMV (stage-wrap)', tool=TOOL['NMV'], error='NMV-E1: Charon succeeds, Aeneas fails during field projection of opaque AccountInfo: "Can\'t retrieve the variants of non-adt type ... solana_account_info::AccountInfo" (actual snapshot; not a guard-drop diagnostic)',
                                            scope='NMV_E001/E002 (evidence/stage-wrap-20261111/NMV_FINDINGS.md NMV-E1)'),
                                       dict(job='NMV (stage-wrap)', tool=TOOL['NMV'], error='Charon PASS, Aeneas exit 2 with internal Not_found at InterpReduceCollapse.collapse_ctx_following_sequence while joining contexts, on the guard-free fission copy (E003/L081 both wrappers; E004/L082 stage2 alone). Two-extraction allowance spent; generic-log extraction family retired.',
                                            scope='NMV_E003, NMV_E004 (evidence/stage-wrap-20261111/NMV_FINDINGS.md NMV-E2, NMV_HANDOFF.md L081/L082)')],
                             evidence=ev('entry-sdk-20261108/NJN_FAILING_STEP.md', 'entry-sdk-20261108/NJN_EXTRACTION_PINS.json', 'stage-wrap-20261111/NMV_FINDINGS.md', 'stage-wrap-20261111/NMV_HANDOFF.md',
                                         'stage-wrap-20261111/NMV_E003/NMV_FISSION_EXTRACTION_PINS.json', 'stage-wrap-20261111/NMV_E004/NMV_FISSION_EXTRACTION_PINS.json'),
                             note='no gate definition named stage1/stage2 exists in the cone (only stage1_owned/stage2_owned, which are different functions): UNMAPPED, no cone key; the ledger rows are the item rows. Other recorded failures in this class: NJH_ guard drop, NLD_ tx1-entry (C3-BIN lead note (be)(1)-(2)); NJM_ E001 add_shared_borrows InterpReduceCollapse.ml:1880 on the owned TX1:129 claims reference (an own reference, not a frozen function); NGA_ InterpBorrows.ml:2731 on qm31_accumulate_product_channels (slice-d-field2-20261104; certified by route (ah), not in the cone as an unextractable function).'))
    # keys for each entry
    PCWL_ST = J(E + 'prov-p5c-20261110/PCWL_STATUS.json')['definitions']
    pcwl_ccs = sorted(x['module'] + '|' + x['definition'] for x in PCWL_ST if x['module'] == 'CurrentClaimSumModel' and 'CANNOT_EXTRACT' in str(x.get('cause', '')))
    pcwl_s1 = sorted(x['module'] + '|' + x['definition'] for x in PCWL_ST if x['module'].startswith('S1Claim') and 'CANNOT_EXTRACT' in str(x.get('cause', '')))
    pcwl_rda = sorted(x['module'] + '|' + x['definition'] for x in PCWL_ST if 'require_distinct_accounts' in x['definition'] and 'CANNOT_EXTRACT' in str(x.get('cause', '')))
    pcwm_ce = sorted(k for k, v in J(E + 'prov-p5d-20261110/PCWM_STATUS.json')['definitions'].items() if 'CANNOT_EXTRACT' in str(v.get('cause', '')))
    pcwn_ce = 'PCWN open_by_cause CANNOT_EXTRACT: 6 (the CurrentClaimDotModel six, already in the PCXM Table 2 group)'
    L1, L2 = set(), set()
    key_rows = collections.defaultdict(set)
    for rw, ks in rowdefs.items():
        for k in ks: key_rows[k].add(rw)
    for it in CE_ITEMS:
        groups = []
        if it['t2']:
            ks = T2keys(it['t2'])
            groups.append(dict(group='PCXM Table 2 name match: ' + it['t2'], layer='L1', keys=ks)); L1 |= set(ks)
        for gname, ks in it.pop('extra_groups', []):
            if ks == 'PCWL_CCS': ks = pcwl_ccs
            if ks == 'PCWL_S1': ks = pcwl_s1
            lay = 'L1' if isinstance(ks, list) and set(ks) <= set(k for t in PCXM['table2'] for k in t['keys_in_cone']) else 'L2'
            groups.append(dict(group=gname, layer=lay, keys=ks))
            (L1 if lay == 'L1' else L2).update(ks)
        # PCWL status keys for require_distinct_accounts / PCWM semantic keys that PCXM did not name
        if it['function'].endswith('require_distinct_accounts'):
            extra = [k for k in pcwl_rda if k not in set(it.get('_k', []))]
            groups.append(dict(group='PCWL_STATUS cause CANNOT_EXTRACT (require_distinct_accounts + 3 loop items)', layer='L1' if set(pcwl_rda) <= set(k for t in PCXM['table2'] for k in t['keys_in_cone']) else 'L2', keys=pcwl_rda))
            (L1 if set(pcwl_rda) <= set(k for t in PCXM['table2'] for k in t['keys_in_cone']) else L2).update(pcwl_rda)
        it['key_groups'] = groups
    # PCWM keys not captured by any group (should be inside the semantic eight)
    CE_KEYS = {k for k in (L1 | L2) if k in cone}
    pcwm_missing = [k for k in pcwm_ce if k in cone and k not in CE_KEYS]
    assert not pcwm_missing, pcwm_missing
    L1c = {k for k in L1 if k in cone}
    assert len(L1c) == 41, len(L1c)
    for it in CE_ITEMS:
        ks = sorted({k for g in it['key_groups'] for k in g['keys'] if k in cone})
        it['cone_keys'] = [dict(key=k, class_=cls[k]) for k in ks]
        it['rows_reaching_keys'] = sorted({rw for k in ks for rw in key_rows.get(k, ())})
        it['unmapped'] = not ks
        for rw in it['rows_own']:
            rec = [x for x in item_records if rw in x['rows']]
            it.setdefault('ot_item_specific_key_counts', {})[rw] = {x['item']: len(x['item_specific_keys']) for x in rec}
        it['status'] = 'CANNOT_EXTRACT' if not str(it.get('category', '')).startswith('EXTRACTION_SHAPE') else 'EXTRACTION_SHAPE_MISS'

    # ---------------------------------------------------------------- 4. blocking lines
    def touched_rows(keys, cmap):
        sk = set(keys)
        out = []
        for rw, ks in rowdefs.items():
            if any(k in sk and (cmap[k] not in SET) for k in ks if k in cmap):
                out.append(rw)
        return sorted(out)

    def blocked(keys, cmap):
        keys = sorted(k for k in set(keys) if k in cone)
        base_rows = rows_settled_only_if([], cmap)['rows_settled_only']
        res = rows_settled_only_if(keys, cmap)
        alone = res['rows_settled_only'] - base_rows
        touched = touched_rows(keys, cmap)
        alone_rows = sorted(set(res['rows']) - set(rows_settled_only_if([], cmap)['rows']))
        return dict(keys_in_set=len(keys), keys_not_settled=sum(1 for k in keys if cmap[k] not in SET), rows_touched=len(touched),
                    blocked_alone=alone, blocked_among_others=len(touched) - alone, alone_rows=alone_rows, touched_rows=touched)

    OT_KEYS = [k for k in cone if cls[k] == 'OPEN_TRANSCRIPTION']
    # also the keys of the OPEN_TRANSCRIPTION items that are not settled (OPEN etc.): the item-level set for the "OPEN_TRANSCRIPTION keys" line
    OT_ITEM_KEYS = sorted({k for it in items for k in (set(it['fn_keys_in_cone']) | set(it['specific_keys'])) if k in cone})
    cmap_before2 = dict(cls)
    for x in reclass: cmap_before2[x['key']] = x['was']
    L1_only = sorted(L1c)
    CE_ALL = sorted(CE_KEYS)
    blk = dict(
        open_transcription_keys=blocked(OT_KEYS, cls),
        open_transcription_item_keys=blocked(OT_ITEM_KEYS, cls),
        cannot_extract_consolidated=blocked(CE_ALL, cls),
        cannot_extract_pcxm_41_on_final_map=blocked(L1_only, cls),
        union_ot_keys_and_ce=blocked(sorted(set(OT_KEYS) | set(CE_ALL)), cls))
    # reproduction of PCXM numbers on the PCXL class map (before any overlay): CE 41 keys alone 6, among 123
    # rebuild the PCXL final map (undo overlays) from the chain: the O1/O2 changes are label-only or recorded, so undo them explicitly
    pre = dict(cls)
    for x in reclass: pre[x['key']] = x['was']
    NOTSET_saved = set(NOTSET)
    NOTSET -= {'HAND_ADAPTED', 'NO_FROZEN_COUNTERPART', 'OPEN_TRANSCRIPTION'}
    pcxm_repro = blocked(sorted(k for k in L1c if True), pre)
    NOTSET.clear(); NOTSET.update(NOTSET_saved)
    cmap = cls
    # own-function CE rows that no CE key touches
    own_rows = sorted({rw for it in CE_ITEMS for rw in it['rows_own']})
    own_not_touched = [rw for rw in own_rows if rw not in blk['cannot_extract_consolidated']['touched_rows']]
    pcxm_repro['note'] = 'PCXM Table 2 (41 keys, 32 unsettled) on the PCXL class map before O1/O2: PCXM reported alone 6 / among 123 (129 rows touched)'
    print('PCXM repro CE-41 on PCXL map: alone %d among %d touched %d' % (pcxm_repro['blocked_alone'], pcxm_repro['blocked_among_others'], pcxm_repro['rows_touched']))

    # ---------------------------------------------------------------- 5. outputs
    fin = snap()
    assert fin['settled'] + fin['not_settled'] + fin['other'] == 1707
    per_class = dict(settled=fin['settled_classes'], not_settled=fin['not_settled_classes'], other=fin['other_classes'])
    headline = dict(settled_of_1707=fin['settled'], not_settled_of_1707=fin['not_settled'], other_of_1707=fin['other'], rows_settled_only_of_599=fin['rows_settled_only'], per_class=per_class)
    # per-key attribution of every change from the PCXL baseline of this recount to the final map
    attrib = []
    for o in overlays:
        attrib.append(dict(overlay=o['name'], delta=o['delta'], n_keys=len(o['keys']), keys=o['keys']))
    def so_rows(cmap_):
        rs = row_status(cmap_)
        return {r for r, t in rs.items() if t['N'] == 0 and t['O'] == 0 and t['U'] == 0 and t['S'] > 0}
    NOTSET_saved = set(NOTSET); NOTSET -= {'HAND_ADAPTED', 'NO_FROZEN_COUNTERPART', 'OPEN_TRANSCRIPTION'}
    rows_before = so_rows(pre); NOTSET.clear(); NOTSET.update(NOTSET_saved)
    rows_after = so_rows(cls)
    row_loss = sorted(rows_before - rows_after)
    # which keys cost each lost row
    row_loss_keys = {rw: sorted(k for k in rowdefs[rw] if cls.get(k) == 'OPEN_TRANSCRIPTION') for rw in row_loss}
    assert not (rows_after - rows_before)

    counts = dict(schema='PCXN_COUNTS/1', target_established=False, research_head=research_head, frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
                  reproduction_of_PCXL=dict(expected='1150/420/137, rows 122', got=REPRO, status='REPRODUCED EXACTLY (assert)'),
                  merged_jobs_after_d80d89716a0=MERGED_AFTER_D80,
                  chain_per_job=[dict(job=j['job'], prefix=j['prefix'], settled=j['after']['settled'], not_settled=j['after']['not_settled'], other=j['after']['other'], rows_settled_only=j['after']['rows_settled_only']) for j in log],
                  overlays=[{k: v for k, v in o.items() if k != 'keys'} | {'n_keys': len(o['keys'])} for o in overlays],
                  headline=headline,
                  rows_lost_to_open_transcription=dict(rows=row_loss, count=len(row_loss), keys_per_row=row_loss_keys, rows_before=len(rows_before), rows_after=len(rows_after)),
                  blocking=blk, pcxm_reproduction_on_pcxl_map=pcxm_repro,
                  ce_own_function_rows_not_touched_by_any_ce_key=own_not_touched,
                  ce_key_layers=dict(L1_pcxm_table2=len(L1c), L2_added_from_status_cause=len({k for k in L2 if k in cone} - L1c), consolidated=len(CE_KEYS),
                                     L2_keys=sorted({k for k in L2 if k in cone} - L1c)),
                  ce_overlap_with_ot_keys=sorted(set(OT_KEYS) & CE_KEYS),
                  open_transcription=dict(items=item_records, items_unmapped=unmapped_items, keys_reclassified=reclass, key_count=len(reclass),
                                          sensitivity_all_receipted_settled_keys_in_items_own_rows_baseline=len(sens_ub),
                                          sensitivity_note='upper bound: every key of the items\' own ledger rows whose baseline class was a receipt credit; the headline uses fn keys + item-specific keys only'),
                  attribution=attrib,
                  unmatched_chain=len(unmatched), conflicts_chain=len(conflicts))
    json.dump(counts, open(os.path.join(OUT, 'PCXN_COUNTS.json'), 'w'), indent=1); open(os.path.join(OUT, 'PCXN_COUNTS.json'), 'a').write('\n')

    ce_doc = dict(schema='PCXN_CANNOT_EXTRACT/1', target_established=False, research_head=research_head,
                  statement='Functions no tool has extracted (Charon + Aeneas, any recorded version) with the tool error, version, evidence, cone keys and rows. A failure is a tool failure, not a proof; every item is OPEN. No ledger row, trust row, RSL or contract was changed.',
                  removed_from_cannot_extract=[dict(item='public_bytes', reason='PCWN item1: fresh = gate EQUALITY_PROVED (PRVEq_PB_w3.lean, PCWN_L004); evidence/prov-p5e-20261110/PCWN_STATUS.json')],
                  key_set=dict(consolidated_keys=len(CE_KEYS), layers=counts['ce_key_layers'], classes=dict(collections.Counter(cls[k] for k in CE_KEYS))),
                  blocking_on_final_map=dict(consolidated={k: v for k, v in blk['cannot_extract_consolidated'].items() if k not in ('touched_rows', 'alone_rows')},
                                             pcxm_41={k: v for k, v in blk['cannot_extract_pcxm_41_on_final_map'].items() if k not in ('touched_rows', 'alone_rows')}),
                  items=CE_ITEMS)
    json.dump(ce_doc, open(os.path.join(OUT, 'PCXN_CANNOT_EXTRACT.json'), 'w'), indent=1); open(os.path.join(OUT, 'PCXN_CANNOT_EXTRACT.json'), 'a').write('\n')
    print('FINAL (PCXN) settled %d not settled %d other %d rows %d | OT keys %d rows alone %d among %d | CE keys %d rows alone %d among %d' % (
        fin['settled'], fin['not_settled'], fin['other'], fin['rows_settled_only'], len(OT_KEYS), blk['open_transcription_keys']['blocked_alone'], blk['open_transcription_keys']['blocked_among_others'],
        len(CE_KEYS), blk['cannot_extract_consolidated']['blocked_alone'], blk['cannot_extract_consolidated']['blocked_among_others']))
