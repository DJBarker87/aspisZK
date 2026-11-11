#!/usr/bin/env python3
"""PCXO_recount.py (P6l): PCXN_recount.py (P6k, evidence/prov-p6k-20261110, copied; stage A reproduces it) plus stage B (jobs merged after the PCXN pin, overlay A HM-O, overlay B parse_blocks).
The PCXN docstring follows.

PCXN_recount.py (P6k): PCXL_recount.py (P6i, copied unchanged up to the chain) extended with the Stream A lead overlays of 2026-11-10.
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
ap.add_argument('--outdir', default='evidence/prov-p6l-20261110', help='PCXO outputs are written here (run from the worktree root)')
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
    # PCXO: research has moved since the PCXN pin 6c8f7bb1b3d; the dirs merged since are P5g (PCWQ_), P6k (PCXN_ itself), P7a (PCWT_), P5i (PCWS_), P8a (PCWU_); stage B adapts them
    EXPECT_UNCHAINED = ['evidence/prov-p5f-20261110', 'evidence/prov-p5g-20261110', 'evidence/prov-p5h-20261110', 'evidence/prov-p5i-20261110', 'evidence/prov-p5j-20261110', 'evidence/prov-p5k-20261110',
                        'evidence/prov-p5l-20261110', 'evidence/prov-p6j-20261110', 'evidence/prov-p6k-20261110', 'evidence/prov-p6m-20261110', 'evidence/prov-p7a-20261110', 'evidence/prov-p8a-20261110']
    assert unchained == EXPECT_UNCHAINED, ('a new evidence dir was merged on research since PCXO was written; it needs an adapter or an explicit no-adapter note', sorted(set(unchained) ^ set(EXPECT_UNCHAINED)))
    unchained_stageB = ['evidence/prov-p5g-20261110', 'evidence/prov-p7a-20261110', 'evidence/prov-p5i-20261110', 'evidence/prov-p8a-20261110', 'evidence/prov-p5j-20261110', 'evidence/prov-p5k-20261110', 'evidence/prov-p5l-20261110']
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
    STAGE_A = dict(counts=counts)   # PCXO: stage A is the PCXN reproduction, compared in memory with the committed PCXN_COUNTS.json (stage B)

    ce_doc = dict(schema='PCXN_CANNOT_EXTRACT/1', target_established=False, research_head=research_head,
                  statement='Functions no tool has extracted (Charon + Aeneas, any recorded version) with the tool error, version, evidence, cone keys and rows. A failure is a tool failure, not a proof; every item is OPEN. No ledger row, trust row, RSL or contract was changed.',
                  removed_from_cannot_extract=[dict(item='public_bytes', reason='PCWN item1: fresh = gate EQUALITY_PROVED (PRVEq_PB_w3.lean, PCWN_L004); evidence/prov-p5e-20261110/PCWN_STATUS.json')],
                  key_set=dict(consolidated_keys=len(CE_KEYS), layers=counts['ce_key_layers'], classes=dict(collections.Counter(cls[k] for k in CE_KEYS))),
                  blocking_on_final_map=dict(consolidated={k: v for k, v in blk['cannot_extract_consolidated'].items() if k not in ('touched_rows', 'alone_rows')},
                                             pcxm_41={k: v for k, v in blk['cannot_extract_pcxm_41_on_final_map'].items() if k not in ('touched_rows', 'alone_rows')}),
                  items=CE_ITEMS)
    STAGE_A['ce_doc'] = ce_doc
    print('FINAL (PCXN) settled %d not settled %d other %d rows %d | OT keys %d rows alone %d among %d | CE keys %d rows alone %d among %d' % (
        fin['settled'], fin['not_settled'], fin['other'], fin['rows_settled_only'], len(OT_KEYS), blk['open_transcription_keys']['blocked_alone'], blk['open_transcription_keys']['blocked_among_others'],
        len(CE_KEYS), blk['cannot_extract_consolidated']['blocked_alone'], blk['cannot_extract_consolidated']['blocked_among_others']))


# =====================================================================================================================
# PCXO stage B (P6l) starts here. Stage A above is PCXN_recount.py (P6k) with the research ref read at the current head.
# =====================================================================================================================
print('STAGE A done', fin['settled'], fin['not_settled'], fin['other'], fin['rows_settled_only'])

# ---------------------------------------------------------------- B0. stage A is the PCXN reproduction: compare with the committed PCXN_COUNTS.json
PCXN_C = J(E + 'prov-p6k-20261110/PCXN_COUNTS.json')
assert (fin['settled'], fin['not_settled'], fin['other'], fin['rows_settled_only']) == (1127, 441, 139, 122)
assert STAGE_A['counts']['headline'] == PCXN_C['headline'], 'stage A headline differs from the committed PCXN_COUNTS.json'
assert STAGE_A['counts']['blocking'] == PCXN_C['blocking'], 'stage A blocking lines differ from the committed PCXN_COUNTS.json'
print('STAGE A == committed PCXN_COUNTS.json (headline, per-class, blocking lines): reproduced')
CLS_PCXN = dict(cls)          # the reproduced PCXN class map (all overlays O1, O2, P5f, P5h applied)
NUM_PCXN = snap()
STAGE_B_LOG_START = len(log)


# ---------------------------------------------------------------- B1. adapters for jobs merged on research after the PCXN pin, in merge order
def a_PCWQ():
    st = S('PCWQ', 'prov-p5g-20261110', 'STATUS')
    lc = st['lead_classes']
    recs = []; cnt = collections.Counter()
    for k, v in lc.items():
        new = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB'}.get(v, v); cnt[new] += 1
        recs.append(assign('PCWQ', k, new, 'PCWQ lead_classes ' + v))
    notes = ['lead_classes applied as given (checkpoint path conditional: domain S2/next=10/64 weights, into_iter parameter, to_le_bytes binding)',
             'STATUS counts (EQUALITY_PROVED 1, DEPENDS_ON_LIBRARY_TRUST 15, GATE_ONLY_HELPER 8) are the job classes; the lead_classes field supersedes them (23 CONDITIONAL_ON_BINDING)']
    # type isomorphisms of the Types module (STATUS type_isomorphism list): keys resolved only if unique in the baseline
    ti = []
    for t in st['type_isomorphism']:
        ti.append(dict(type=t['type'], theorem=t['theorem'], file=t['file']))
    notes.append('STATUS type_isomorphism lists %d type equivalences (%s); they are checked against the baseline universe below and applied only when the key resolves uniquely' % (len(ti), ', '.join(t['type'] for t in ti)))
    return recs, notes, dict(lead_classes=len(lc), by_class=dict(cnt), type_isomorphisms_listed=len(ti))


def a_PCWT():
    st = S('PCWT', 'prov-p7a-20261110', 'STATUS')
    recs = []; cnt = collections.Counter()
    for k, v in st['records'].items():
        lcl = v['lead_class']
        new = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB'}.get(lcl, lcl); cnt[new] += 1
        hm = None
        if lcl == 'DEPENDS_ON_LIBRARY_TRUST':
            hm = sorted({t.split(' ')[0] for t in (v.get('trust_rows') or [])}) or None
            if not hm: hm_job_level.append(dict(job='PCWT', key=k, text='DEPENDS_ON_LIBRARY_TRUST without trust_rows in the record'))
        recs.append(assign('PCWT', k, new, 'PCWT lead_class %s (status class_ %s; theorem %s)' % (lcl, v['class_'], v.get('theorem')), hm=hm))
    notes = ['lead_class applied per record; status class_ differs for %d records (16 instance-identity records stay CONDITIONAL_ON_BINDING per lead_corrections)' % sum(1 for v in st['records'].values() if v['class_'] != v['lead_class'])]
    return recs, notes, dict(records=len(st['records']), by_lead_class=dict(cnt))


def a_PCWS():
    st = S('PCWS', 'prov-p5i-20261110', 'STATUS')
    recs = []; cnt = collections.Counter(); notes = []
    for x in st['definitions']:
        lcl = x['lead_class']
        new = {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB'}.get(lcl, lcl); cnt[new] += 1
        hm = (sorted(set(re.findall(r'HM-[A-G]', json.dumps(x)))) or None) if lcl == 'DEPENDS_ON_LIBRARY_TRUST' else None
        k = x['module'] + '|' + x['definition']
        r = assign('PCWS', k, new, 'PCWS lead_class ' + lcl + ' (status ' + x['status'] + ')', hm=hm)
        recs.append(r)
    notes.append('lead_class applied per definition; the four NJS_Extract equalities are OFF_EMISSION_WRAPPING_ACCEPTED (OFF emission of a wrapping gate)')
    notes.append('CANNOT_EXTRACT keys (13: AspisR1TerminalDecoder 10, AspisR1DecodeKFullV10 3) keep their baseline not-settled/OPEN class: the class CANNOT_EXTRACT is a not-settled label (NOTSET) and is added to the CE key set in stage B')
    return recs, notes, dict(definitions=len(st['definitions']), by_lead_class=dict(cnt))


def a_PCWU():
    st = S('PCWU', 'prov-p8a-20261110', 'STATUS')
    recs = []; notes = []; cnt = collections.Counter()
    for x in st['credited']:
        k = x['module'] + '|' + x['definition']
        s0 = x['status']
        new = 'TYPE_ISOMORPHISM' if 'structure equiv' in s0 else {'EQUALITY_PROVED': 'EQUALITY_PROVED_JOB', 'CONDITIONAL_ON_BINDING': 'CONDITIONAL_ON_BINDING'}.get(s0, s0)
        cnt[new] += 1
        recs.append(assign('PCWU', k, new, 'PCWU STATUS credited ' + s0))
    notes.append('PCWU STATUS has no lead_classes field: its credited records are applied as given; the structure Equiv is TYPE_ISOMORPHISM per the standing Equiv rule; items under not_credited (dot_push_entry, option_context_anchor, stage1/stage2/snapshot, prepared_claim) change no class')
    return recs, notes, dict(credited=len(st['credited']), not_credited=len(st['not_credited']), by_class=dict(cnt))


def a_noop(pre, d, what):
    def f():
        st = S(pre, d, 'STATUS')
        return [], ['%s: %s (STATUS read; no per-key credit)' % (pre, what)], dict(records=0)
    return f


STAGE_B_JOBS = [('p5g', 'PCWQ', 'prov-p5g-20261110', a_PCWQ), ('p7a', 'PCWT', 'prov-p7a-20261110', a_PCWT), ('p5i', 'PCWS', 'prov-p5i-20261110', a_PCWS),
                ('p8a', 'PCWU', 'prov-p8a-20261110', a_PCWU),
                ('p5j', 'PCWV', 'prov-p5j-20261110', a_noop('PCWV', 'prov-p5j-20261110', 'paused for PIN2, no equality proved, no Lean scope, nine S8OwnedP6 keys OPEN')),
                ('p5k', 'PCWW', 'prov-p5k-20261110', a_noop('PCWW', 'prov-p5k-20261110', 'paused, all listed keys OPEN with causes')),
                ('p5l', 'PCWX', 'prov-p5l-20261110', a_noop('PCWX', 'prov-p5l-20261110', 'paused before any scope; its 24 definitions repeat the PCWQ_ lead classes'))]
for job, pre, d, fn in STAGE_B_JOBS:
    run_job(job, pre, d, fn)
N_JOBS = snap()
print('STAGE B jobs ->', N_JOBS['settled'], N_JOBS['not_settled'], N_JOBS['other'], 'rows', N_JOBS['rows_settled_only'], 'unmatched total', len(unmatched), 'conflicts', len(conflicts))
for u in unmatched[-10:]: print('  UNMATCHED', json.dumps(u)[:200])
for c in conflicts[-6:]: print('  CONFLICT', json.dumps(c)[:260])


# =====================================================================================================================
# B2. overlay (B): generator parse_blocks audit (Stream A lead ruling B)
# =====================================================================================================================
import hashlib
sys.dont_write_bytecode = True


class GitBatch:
    """one persistent `git cat-file --batch` process, pinned to REF (same commit as every other read in this run)"""
    def __init__(self, ref):
        self.p = subprocess.Popen(['git', 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.ref = ref; self.cache = {}

    def blob(self, path):
        if path in self.cache: return self.cache[path]
        self.p.stdin.write((self.ref + ':' + path + '\n').encode()); self.p.stdin.flush()
        h = self.p.stdout.readline().decode().split()
        if len(h) < 3 or h[1] == 'missing': r = None
        else:
            n = int(h[2]); r = self.p.stdout.read(n); self.p.stdout.read(1)
        self.cache[path] = r
        return r

    def text(self, path):
        b = self.blob(path)
        return None if b is None else b.decode('utf-8', 'replace')


GB = GitBatch(REF)
ALLFILES = [f for f in subprocess.run(['git', 'ls-tree', '-r', '--name-only', REF, 'evidence'], capture_output=True, check=True).stdout.decode().split('\n') if f]
print('files under evidence/ at', REF[:12], len(ALLFILES))


def uncomment(s):
    out = []; i = 0; depth = 0; string = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; out += [' ', ' ']; i += 2
            elif s.startswith('-/', i): depth -= 1; out += [' ', ' ']; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif string:
            if s[i] == '\\' and i + 1 < len(s): out += [' ', ' ']; i += 2
            elif s[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif s.startswith('/-', i): depth = 1; out += [' ', ' ']; i += 2
        elif s.startswith('--', i):
            end = s.find('\n', i); end = len(s) if end < 0 else end; out.extend(' ' * (end - i)); i = end
        elif s[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(s[i]); i += 1
    return ''.join(out)


KW_D = r'(?:def|abbrev|structure|inductive|impl_def|opaque|axiom|theorem|instance|class)'


def split_attr(clean):
    i = 0; attrs = []
    while True:
        m = re.match(r'\s*@\[', clean[i:])
        if not m: break
        j = i + m.end(); depth = 1; k = j
        while k < len(clean) and depth:
            if clean[k] == '[': depth += 1
            elif clean[k] == ']': depth -= 1
            k += 1
        attrs.append(clean[j:k - 1]); i = k
    return attrs, clean[i:]


PEEL = {'A': None,
        'B': r'(?:namespace|section|open|set_option|variable|universe|noncomputable section)',
        'C': r'(?:import|namespace|section|open|set_option|variable|universe|noncomputable section)'}


def parse_decl_names(text, variant):
    """parse_blocks of the generator lineage reduced to the recognised declaration names (kind == decl), per variant:
    A = no peeling (PCO_ .. PCUD_, PCWA_ .. PCWE_, PCT_), B = peels namespace/section/open/set_option/variable/universe (PCQH_ .. PCWN_, PCWR_, PCWS_, PCWT_), C = also peels import (PCWP_, the fix)."""
    clean = uncomment(text)
    raw_blocks = re.split(r'\n[ \t]*\n', text)
    pos = 0; names = []
    hdr = PEEL[variant]
    for rb in raw_blocks:
        start = text.find(rb, pos); end = start + len(rb); pos = end
        while hdr:
            m0 = re.match(r'[ \t]*' + hdr + r'\b[^\n]*\n', rb)
            if not m0 or '\n' not in rb[m0.end():] and not rb[m0.end():].strip(): break
            start += m0.end(); rb = rb[m0.end():]
        cb = clean[start:end]
        attrs, rest = split_attr(cb)
        m = re.match(r'\s*((?:noncomputable|private|protected|partial|unsafe|nonrec)\s+)*(' + KW_D + r')\s+(?:\([^)]*\)\s*)?([^\s({:\[]+)', rest)
        if m and re.match(r'\s*(?:/--|@\[|(?:noncomputable|private|protected|partial|unsafe|nonrec|' + KW_D[3:-1] + r')\b)', rb) or (m and rb.lstrip().startswith(('/--', '@['))):
            names.append((m.group(3), text[:start].count('\n') + 1))
    return names


# --- generators: variant by the text of their parse_blocks
GEN_FILES = [f for f in ALLFILES if f.endswith('_gen_equalities.py')]
GEN_VARIANT = {}; GEN_SHA = {}
for f in GEN_FILES:
    t = GB.text(f)
    body = re.search(r'def parse_blocks\(text\):.*?(?=\ndef )', t, re.S).group(0)
    v = 'A' if 'm0 = re.match' not in body else ('C' if '(?:import|namespace' in body else 'B')
    GEN_VARIANT[f] = v; GEN_SHA[f] = hashlib.sha256(GB.blob(f)).hexdigest()
GEN_BY_NAME = collections.defaultdict(list)
for f, v in GEN_VARIANT.items(): GEN_BY_NAME[f.split('/')[-1]].append((f, v))
FIX_FILE = 'evidence/prov-p5f-20261110/PCWP_gen_equalities.py'
assert GEN_VARIANT[FIX_FILE] == 'C'
print('generator variants:', collections.Counter(GEN_VARIANT.values()), '| fixed generator', FIX_FILE, GEN_SHA[FIX_FILE][:16])

# --- (generator, gate module) pairs: every PRVEq_*.lean file written by a generator names it in its first line
PRV_FILES = [f for f in ALLFILES if re.search(r'/PRVEq[^/]*\.lean$', f)]
BUNDLES = [f for f in PRV_FILES if re.search(r'/PRVEq_bundle_', f)]   # compile vehicles: exact concatenations of member files that carry their own generator headers
PAIRS = collections.defaultdict(set)      # (generator name, module) -> set of PRVEq file paths
hdr_re = re.compile(r'^-- GENERATED by (\S+_gen_equalities\.py) for gate module (\S+)', re.M)
n_hdr = 0
for f in PRV_FILES:
    if f in set(BUNDLES): continue
    b = GB.blob(f)
    if b is None: continue
    m = hdr_re.search(b[:600].decode('utf-8', 'replace') + ' ')
    if m: PAIRS[(m.group(1), m.group(2).rstrip('.,;'))].add(f); n_hdr += 1
print('PRVEq files', len(PRV_FILES), 'with generator header', n_hdr, 'distinct (generator, module) pairs', len(PAIRS))
norm = lambda s_: re.sub(r'[._]', '', s_)
GATE_FILES = [f for f in ALLFILES if f.endswith('.lean') and re.search(r'(?:/inputs/gate_|/gate_sources/|/gate_src/|/gate/|/gate_)[^/]*\.lean$', f)]
print('gate source copies', len(GATE_FILES))

PLAN_ENTRIES = json.load(open(args.outdir + '/PCXO_PLAN_ENTRIES.json'))   # cached by PCXO_citations.py --fetch (read-only ssh of the listed modules' entries)
GATE_BY_NORM = collections.defaultdict(list)
for f in GATE_FILES:
    stem = f.split('/')[-1][:-5]
    stem = re.sub(r'^gate_', '', stem)
    stem = re.sub(r'_ctl\d+$', '', stem)
    GATE_BY_NORM[norm(stem)].append(f)
jobdir = lambda f: f.split('/')[1]
AUDIT_ROWS = []          # one row per (generator, module, gate-source blob) with its dropped declarations
NO_GATE_SOURCE = []
seen_pairs = set()
for (g, m), files in sorted(PAIRS.items()):
    gv = {v for _, v in GEN_BY_NAME.get(g, [])}
    assert len(gv) == 1, (g, gv)
    v = next(iter(gv))
    dirs = {jobdir(f) for f in files}
    cands = GATE_BY_NORM.get(norm(m), [])
    same = [c for c in cands if jobdir(c) in dirs]
    use = same or cands
    plan_used = False
    if not use:
        pe_ = PLAN_ENTRIES['entries'].get(m)
        if pe_:
            pp = pe_['source']['path']
            if GB.blob(pp) is not None: use = [pp]; plan_used = True
    if not use:
        NO_GATE_SOURCE.append(dict(generator=g, variant=v, module=m, prez=sorted(dirs))); continue
    shas = {}
    for c in use: shas.setdefault(hashlib.sha256(GB.blob(c)).hexdigest(), []).append(c)
    for sha_, cs in sorted(shas.items()):
        t = GB.text(cs[0])
        Cn = parse_decl_names(t, 'C'); Vn = {n for n, _ in parse_decl_names(t, v)}
        dropped = [(n, ln) for n, ln in Cn if n not in Vn]
        AUDIT_ROWS.append(dict(generator=g, variant=v, module=m, gate_source=cs[0], gate_source_sha256=sha_, copies=len(cs), source_in_job_dir=bool(same), dropped=dropped, decls_fixed=len(Cn), source_is_l187_plan=plan_used))


# --- exit-0 scopes: theorem names printed by `#print axioms` in an exit-0 lean receipt (receipt.json of every job)
RECEIPTS = [f for f in ALLFILES if f.endswith('/receipt.json') and '/prov-p' in f]
EXIT0_THMS = collections.defaultdict(list)       # theorem name -> [(receipt, standard axioms only?)]
n_rc = 0
for f in RECEIPTS:
    try: r = json.loads(GB.text(f))
    except Exception: continue
    if r.get('kind') != 'lean' or r.get('exit_status') != 0: continue
    n_rc += 1
    pa = r.get('print_axioms') or []
    if isinstance(pa, str): pa = [pa]
    for ln in pa:
        for mm in AX.finditer(ln):
            ax = {a.strip() for a in (mm.group(2) or '').replace('\n', ' ').split(',') if a.strip()}
            EXIT0_THMS[mm.group(1)].append((f, ax <= STD))
EXIT0_STD = {t for t, v in EXIT0_THMS.items() if any(ok for _, ok in v)}
EXIT0_PRVEQ_N = [(t, norm(t)) for t in EXIT0_STD if t.startswith('PRVEq.')]
print('exit-0 lean receipts', n_rc, 'theorem names printed', len(EXIT0_THMS), 'with standard axioms only', len(EXIT0_STD))

# --- theorems each key is credited with, from the recorded provenance (PCXD_PROVENANCE) and the job adapters of this run (the `why` strings carry the theorem name)
PD = J(E + 'prov-p6r-20261110/PCXD_PROVENANCE.json')['modules']
RECORDED = collections.defaultdict(set)
for m_, mm_ in PD.items():
    for d_, r_ in mm_['definitions'].items():
        if r_.get('theorem'): RECORDED[m_ + '|' + d_].add(r_['theorem'])
for j_ in log:
    for ch in j_['change_list']:
        for t_ in re.findall(r'(PRV[A-Za-z0-9_]*\.[A-Za-z0-9_.]+)', ch.get('why', '')): RECORDED[ch['key']].add(t_)


# --- statement index: every `theorem N : @FRESH = @GATE` of every PRVEq file (dedupe by blob); GATE is the full gate name = the definition part of the key
THM_RE = re.compile(r'(?m)^theorem\s+(\S+)\s*:\s*@(\S+)\s*=\s*@(\S+?)\s*:=')
NS_TOKEN = re.compile(r'(?m)^(namespace|end)\s+(\S+)\s*$|^theorem\s+(\S+)\s*:\s*@(\S+)\s*=\s*@(\S+?)\s*:=')


def thm_statements(text):
    """(full theorem name, fresh lhs, gate rhs) for every `theorem N : @A = @B :=` of the file; N is completed by the enclosing `namespace` stack"""
    stack = []; out = []
    for mm in NS_TOKEN.finditer(text):
        if mm.group(1) == 'namespace': stack.append(mm.group(2))
        elif mm.group(1) == 'end':
            if stack and stack[-1] == mm.group(2): stack.pop()
        elif mm.group(3):
            full = '.'.join(stack + [mm.group(3)]) if not mm.group(3).startswith('_root_.') else mm.group(3)[7:]
            out.append((full, mm.group(4), mm.group(5)))
    return out


GATE_THMS = collections.defaultdict(set)
THM_INFO = collections.defaultdict(list)      # gate name -> [(full theorem name, fresh lhs, first file carrying that blob)]
_seen_blob = set()
for f in PRV_FILES:
    b = GB.blob(f)
    if b is None: continue
    h_ = hashlib.sha256(b).digest()
    if h_ in _seen_blob: continue
    _seen_blob.add(h_)
    for full, lhs, rhs in thm_statements(b.decode('utf-8', 'replace')):
        GATE_THMS[rhs].add(full); THM_INFO[rhs].append((full, lhs, f))
print('PRVEq theorem statements indexed by gate name', sum(len(v) for v in GATE_THMS.values()), 'distinct gate names', len(GATE_THMS))


def theorem_evidence(key, module, decl):
    """exit-0 standard-axioms theorems naming the key: (i) the theorem recorded for the key, (ii) a PRVEq theorem whose statement right-hand side is exactly the key's gate definition name"""
    d_full = key.split('|', 1)[1]
    rec = sorted(t for t in RECORDED.get(key, ()) if t in EXIT0_STD)
    q = sorted(t for t in GATE_THMS.get(d_full, ()) if t in EXIT0_STD)
    return rec, q


BASE_MODS = collections.defaultdict(list)
for k in base:
    m_, d_ = k.split('|', 1); BASE_MODS[norm(m_)].append((m_, d_))


def keys_of(module, decl):
    return sorted({m_ + '|' + d_ for m_, d_ in BASE_MODS.get(norm(module), []) if d_ == decl or d_.endswith('.' + decl)})


# --- fresh-emission side of the same defect (informational and applied): a fresh Funs/Types text parsed by the generator of its job directory
A_DIRS = {f.split('/')[1] for f, v in GEN_VARIANT.items() if v == 'A'}
FR = [f for f in ALLFILES if re.search(r'/prov-p[^/]*/.*/(Funs|Types)\.lean$', f)]
FRESH_ROWS = []; seen_sha = set()
for f in FR:
    b = GB.blob(f); sh_ = hashlib.sha256(b).hexdigest()
    if sh_ in seen_sha: continue
    seen_sha.add(sh_)
    t = b.decode('utf-8', 'replace'); v = 'A' if f.split('/')[1] in A_DIRS else 'B'
    vn = {x for x, _ in parse_decl_names(t, v)}
    d = [(n, ln) for n, ln in parse_decl_names(t, 'C') if n not in vn]
    if d:
        mod = re.sub(r'_ctl\d+$', '', f.split('/')[-2].replace('fresh_CTL_', '').replace('fresh_', ''))
        FRESH_ROWS.append(dict(fresh_source=f, fresh_sha256=sh_, variant=v, module_guess=mod, dropped=d))

PB = []          # one record per (side, module, dropped declaration): keys, class now, theorem evidence, action
def pb_record(side, module, generator, variant, source, sha_, dn, ln):
    ks = keys_of(module, dn)
    recs = []
    if not ks:
        return [dict(side=side, module=module, generator=generator, variant=variant, source=source, source_sha256=sha_, first_line=ln, dropped_declaration=dn, key=None, class_now=None,
                     credited=False, theorem_found=None, action='none: not a definition key of the 1876-key universe (type, trait or helper declaration outside the counted keys)')]
    for k in ks:
        c0 = cls.get(k); credited = c0 is not None and kind(c0) != 'N'
        rec, q = theorem_evidence(k, module, dn)
        found = bool(rec or q)
        if not credited: act = 'none: key not credited (class %s)' % c0
        elif found: act = 'none: credited with an exit-0 standard-axioms theorem naming it'
        else: act = 'DEMOTE_TO_OPEN'
        recs.append(dict(side=side, module=module, generator=generator, variant=variant, source=source, source_sha256=sha_, first_line=ln, dropped_declaration=dn, key=k, class_now=c0,
                         credited=credited, theorem_found=found, recorded_theorems=rec, statement_theorems=q[:6], action=act))
    return recs


for r in AUDIT_ROWS:
    for dn, ln in r['dropped']:
        PB.extend(pb_record('gate', r['module'], r['generator'], r['variant'], r['gate_source'], r['gate_source_sha256'], dn, ln))
for r in FRESH_ROWS:
    for dn, ln in r['dropped']:
        PB.extend(pb_record('fresh', r['module_guess'], None, r['variant'], r['fresh_source'], r['fresh_sha256'], dn, ln))
PB_KEYS = {x['key'] for x in PB if x['key']}
DEMOTE = sorted({x['key'] for x in PB if x['action'] == 'DEMOTE_TO_OPEN'})
print('parse_blocks audit: gate rows %d (with a drop %d), fresh files with a drop %d, dropped declarations %d, of which keys %d, credited keys %d, demotions %d, pairs without saved gate source %d' % (
    len(AUDIT_ROWS), sum(1 for r in AUDIT_ROWS if r['dropped']), len(FRESH_ROWS), len(PB), len(PB_KEYS), len({x['key'] for x in PB if x['credited']}), len(DEMOTE), len(NO_GATE_SOURCE)))
for x in PB:
    if x['key']: print('  ', x['side'], x['variant'], (x['generator'] or '')[:5], x['key'][:96], x['class_now'], x['action'][:40])
print('  no saved gate source:', [(n['generator'][:5], n['module']) for n in NO_GATE_SOURCE])


# =====================================================================================================================
# B3. overlay (A): HM-O withdrawn as a trust row (Stream A lead ruling A)
# =====================================================================================================================
LIB_ROOTS = ('core.', 'alloc.', 'std.', 'solana_', 'Slice.', 'Array.', 'MutAArray', 'Vec.', 'Aeneas.', 'Std.', 'Result.', 'Option.')
EXT_CLASS = {}
_E = J(E + 'prov-p6r-20261110/PCXD_EXTERNALS.json')
for sec in 'abc':
    for x in _E[sec]: EXT_CLASS.setdefault(x['name'], x['class_'])
LIB_CLASSES = {'a_sdk_type_models', 'b_core_slice_iterator_model', 'c_core_option_result_combinators', 'd_core_array_slice_ops', 'e_alloc_and_allocator_models', 'f_core_num_ops_iter_models', 'h_s1_values_expand_models'}


def ext_is_aspis_item(name):
    """an external of the fresh emission that is an item of the frozen Aspis source (cross-crate constant or function resolved by name to the gate), not a library/SDK/alloc model"""
    c = EXT_CLASS.get(name)
    if c is not None: return c not in LIB_CLASSES
    return not name.startswith(LIB_ROOTS)


# --- generator report index: fresh namespace -> external_funs (union over the reports of that namespace)
REPORTS = [f for f in ALLFILES if f.endswith('.json') and '/prov-p' in f and re.search(r'report', f.split('/')[-1], re.I)]
REP_EXT = collections.defaultdict(lambda: dict(funs=set(), reports=[]))
n_rep = 0
for f in REPORTS:
    b = GB.blob(f)
    if b is None or b'"external_funs"' not in b: continue
    try: r = json.loads(b)
    except Exception: continue
    ns_ = r.get('fresh_namespace')
    if not ns_ or 'external_funs' not in r: continue
    n_rep += 1
    REP_EXT[ns_]['funs'] |= set(r['external_funs']); REP_EXT[ns_]['reports'].append(f)
print('generator reports with external_funs', n_rep, 'fresh namespaces', len(REP_EXT))
ALL_EXT_FUNS = set(EXT_CLASS)
for v_ in REP_EXT.values(): ALL_EXT_FUNS |= v_['funs']
print('known external function/constant names (generator reports plus PCXD_EXTERNALS)', len(ALL_EXT_FUNS))

# --- file level: fresh namespace, declaration texts (fresh namespace part only), per-file cache
_FILE_CACHE = {}
FRESH_NS_RE = re.compile(r'(?m)^namespace\s+(PRVFresh_\S+)')
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def file_model(path):
    if path in _FILE_CACHE: return _FILE_CACHE[path]
    t = GB.text(path)
    if t is None: _FILE_CACHE[path] = None; return None
    nsm = FRESH_NS_RE.findall(t)
    clean = uncomment(t)
    decls = {}                  # relative name (inside the fresh namespace) -> cleaned code text
    # fresh region(s): from `namespace PRVFresh_X` to its `end PRVFresh_X`
    for ns_ in set(nsm):
        i = 0
        while True:
            a = clean.find('namespace ' + ns_, i)
            if a < 0: break
            z = clean.find('end ' + ns_, a)
            z = len(clean) if z < 0 else z
            seg = clean[a:z]; i = z + 1
            for rb in re.split(r'\n[ \t]*\n', seg):
                body = rb
                while True:
                    m0 = re.match(r'[ \t]*(?:import|namespace|section|open|set_option|variable|universe|noncomputable section)\b[^\n]*\n', body)
                    if not m0 or '\n' not in body[m0.end():] and not body[m0.end():].strip(): break
                    body = body[m0.end():]
                attrs, rest = split_attr(body)
                m = re.match(r'\s*((?:noncomputable|private|protected|partial|unsafe|nonrec)\s+)*(' + KW_D + r')\s+(?:\([^)]*\)\s*)?([^\s({:\[]+)', rest)
                if m: decls.setdefault(m.group(3), []).append(rest)
    have_rep = any(n in REP_EXT for n in nsm)
    ext = set().union(*[REP_EXT[n]['funs'] for n in set(nsm) if n in REP_EXT]) if have_rep else set(ALL_EXT_FUNS)
    _FILE_CACHE[path] = dict(namespaces=sorted(set(nsm)), decls=decls, ext=ext, have_report=have_rep, fallback_free_names=(not have_rep and bool(nsm)))
    return _FILE_CACHE[path]


def closure_externals(fm, start):
    """externals (fresh emission axioms of the report) reached from fresh declaration `start` through the declarations of the same fresh namespace"""
    ext = fm['ext']; decls = fm['decls']
    seen = set(); stack = [start]; hit = {}
    # prefix index of declaration names for dotted-token resolution
    while stack:
        d = stack.pop()
        if d in seen or d not in decls: continue
        seen.add(d)
        for txt in decls[d]:
            for tk in TOKEN_RE.findall(txt):
                tk = tk.rstrip('.')
                # longest declaration/external prefix of the dotted token
                parts = tk.split('.')
                for n in range(len(parts), 0, -1):
                    cand = '.'.join(parts[:n])
                    if cand in decls:      # a declaration of the fresh namespace takes priority over an opened gate name (Lean name resolution)
                        if cand not in seen: stack.append(cand)
                        break
                    if cand in ext: hit.setdefault(cand, []).append(d); break
    return sorted(hit), len(seen)


def fresh_rel(lhs):
    m = re.search(r'PRVFresh_[A-Za-z0-9_]+\.(.+)$', lhs)
    return m.group(1) if m else None


DIR_FILES = collections.defaultdict(list)       # job directory -> PRVEq files of that directory (any depth), deduplicated by blob
_dseen = set()
for f in PRV_FILES:
    if f in set(BUNDLES): pass
    d0 = f.split('/')[1]
    b = GB.blob(f)
    if b is None: continue
    key_ = (d0, hashlib.sha256(b).digest())
    if key_ in _dseen: continue
    _dseen.add(key_); DIR_FILES[d0].append(f)


def imports_of(f):
    t = GB.text(f) or ''
    return set(re.findall(r'(?m)^import\s+(\S+)', t[:6000]))


def hmo_key(k):
    """HM-O evidence for credited key k, from the files of the job that credited it (never from another job's proof of the same definition):
    (1) a theorem of the crediting job whose statement right-hand side is the key's gate definition, or
    (2) a PRVEq file of that job that imports the gate module and has a fresh declaration of that name.
    The externals of the fresh emission (generator report external_funs, else the free-name scan) reached by the fresh declaration through the fresh namespace are returned."""
    m_, d_ = k.split('|', 1)
    jd = CREDIT_DIR.get(k)
    if jd is None: return [], 'NO_CREDITING_JOB'
    cands = []
    seen_f = set()
    for t, lhs, f in THM_INFO.get(d_, []):
        if f.split('/')[1] == jd and t in EXIT0_STD:
            cands.append((t, fresh_rel(lhs), f)); seen_f.add(f)
    if not cands:
        for f in DIR_FILES.get(jd, []):
            if m_ not in imports_of(f): continue
            fm = file_model(f)
            if fm is None: continue
            rels = [r_ for r_ in fm['decls'] if d_ == r_ or d_.endswith('.' + r_)]
            if rels:
                cands.append((None, max(rels, key=len), f))
    out = []
    for t, rel, f in cands:
        fm = file_model(f)
        if fm is None or rel is None or rel not in fm['decls']:
            out.append(dict(theorem=t, file=f, evaluable=False, why='fresh declaration not found in the proving file')); continue
        if not fm['have_report'] and not fm['fallback_free_names']:
            out.append(dict(theorem=t, file=f, evaluable=False, why='no fresh namespace in the proving file and no generator report')); continue
        hits, nd = closure_externals(fm, rel)
        items = [h for h in hits if ext_is_aspis_item(h)]
        libs = [h for h in hits if not ext_is_aspis_item(h)]
        out.append(dict(theorem=t, file=f, evaluable=True, method=('generator report external_funs' if fm['have_report'] else 'free-name scan (file not produced by a generator report): names of known external functions/constants not declared in the fresh namespace'),
                        fresh_namespace=fm['namespaces'], fresh_declaration=rel, closure_declarations=nd, aspis_item_externals=items, library_externals=libs))
    return out, ('THEOREM_STATEMENT' if any(c[0] for c in cands) else ('FRESH_DECLARATION_MATCH' if cands else 'NO_CANDIDATE_IN_CREDITING_JOB'))


PROV_DIRS = sorted({f.split('/')[1] for f in ALLFILES if f.startswith('evidence/prov-p')})
def dir_of_label(lab):
    if not lab: return None
    c = [d for d in PROV_DIRS if d.split('-')[1].lower() == lab.lower()]
    return c[-1] if len(c) == 1 else (c[0] if c else None)
CREDIT_DIR = {}
CREDIT_HOW = {}
for k in cone:
    if cls.get(k) == 'EQUALITY_PROVED_P1N': CREDIT_DIR[k] = 'prov-p1n-20261110'; CREDIT_HOW[k] = 'baseline class EQUALITY_PROVED_P1N (P1n job)'
for k, r_ in ((m_ + '|' + d_, r_) for m_, mm_ in PD.items() for d_, r_ in mm_['definitions'].items()):
    if cls.get(k) not in SET or cls.get(k) in CREDIT_NOT_FRESH: continue
    pf = r_.get('proving_file'); rc = r_.get('receipt')
    if pf and '/' in pf: CREDIT_DIR[k] = pf.split('/')[0]; CREDIT_HOW[k] = 'PCXD proving_file directory'
    elif rc and '/' in rc: CREDIT_DIR[k] = rc.split('/')[0]; CREDIT_HOW[k] = 'PCXD receipt directory'
    elif dir_of_label(r_.get('decided_by')): CREDIT_DIR[k] = dir_of_label(r_['decided_by']); CREDIT_HOW[k] = 'PCXD decided_by job %s' % r_['decided_by']
for j_ in log:
    for ch in j_['change_list']:
        if kind(ch['now']) == 'S': CREDIT_DIR[ch['key']] = j_['dir']; CREDIT_HOW[ch['key']] = 'job adapter %s' % j_['prefix']
IS_TYPE = lambda k: bool(re.search(r'(?:^|[._])Types$|\.Types\b|Types[A-Za-z0-9_]*$', k.split('|')[0])) or any(t.endswith('.equiv') for t in RECORDED.get(k, ()))
STATUS_HINT = {}
_pq = S('PCWQ', 'prov-p5g-20261110', 'STATUS')
for x in _pq['definitions']: STATUS_HINT['RPz7_WAdm_Fissioned_Funs|' + x['key']] = 'PCWQ_ STATUS depends_on: %s' % (x.get('depends_on') or [])
for k_, v_ in S('PCWT', 'prov-p7a-20261110', 'STATUS')['records'].items(): STATUS_HINT[k_] = 'PCWT_ STATUS what_is_bound: %s' % v_.get('what_is_bound', '')[:240]
HMO = {}
for k in sorted(cone):
    if cls[k] not in SET: continue
    ev, basis = hmo_key(k); used_recorded = basis
    evl = [e for e in ev if e['evaluable']]
    if IS_TYPE(k) and not any(e.get('aspis_item_externals') for e in evl):
        verdict = 'HMO_NO'; why = 'type declaration (module of kind Types or an .equiv theorem): no constant or function external can occur; decided by kind, not by an emission scan'
        HMO[k] = dict(verdict=verdict, subkind='TYPE_KEY', why=why, class_before=cls[k], candidates=ev, evidence_basis=used_recorded); continue
    if not ev: verdict = 'HMO_UNDETERMINED'; why = ('credited by class %s through a receipt/pin text equality or without a recorded proving job: no fresh = gate theorem is the credit basis' % cls[k]) if basis == 'NO_CREDITING_JOB' else ('no theorem or fresh declaration of the crediting job (%s) found for this key' % CREDIT_DIR.get(k))
    elif not evl: verdict = 'HMO_UNDETERMINED'; why = '; '.join(sorted({e['why'] for e in ev}))
    elif any(e['aspis_item_externals'] for e in evl): verdict = 'HMO_YES'; why = 'fresh external(s) of Aspis items resolved by name to the gate constants'
    else: verdict = 'HMO_NO'; why = 'no Aspis-item external reached by the fresh closure'
    HMO[k] = dict(verdict=verdict, why=why, class_before=cls[k], candidates=ev, evidence_basis=used_recorded, status_hint=STATUS_HINT.get(k))
tally = collections.Counter((v['class_before'], v['verdict']) for v in HMO.values())
print('HM-O (credited keys %d):' % len(HMO), dict(collections.Counter(v['verdict'] for v in HMO.values())))
for c_ in sorted({a for a, _ in tally}): print('   ', c_.ljust(34), {b: n for (a, b), n in tally.items() if a == c_})

CROSS_CRATE_PREFIXES = ('aspis_', 'fast_pairing.', 'solana_pool', 'aspis-')
def ext_kind(n): return 'cross_crate' if n.startswith(CROSS_CRATE_PREFIXES) else 'own_crate_or_other'
kc = collections.Counter()
for k, v in HMO.items():
    if v['verdict'] != 'HMO_YES': continue
    names = sorted({x for c in v['candidates'] for x in c.get('aspis_item_externals', [])})
    kinds = {ext_kind(n) for n in names}
    v['external_names'] = names; v['external_kinds'] = sorted(kinds)
    kc[tuple(sorted(kinds))] += 1
print('HM-O YES by external kind', dict(kc))
oc = collections.Counter(n for v in HMO.values() if v['verdict'] == 'HMO_YES' for n in v['external_names'] if ext_kind(n) != 'cross_crate')
print('non cross-crate externals', oc.most_common(12))


# =====================================================================================================================
# B4. apply the overlays with separate deltas; recompute the blocking lines on the final map
# =====================================================================================================================
def brief2(n):
    return dict(settled=n['settled'], not_settled=n['not_settled'], other=n['other'], rows_settled_only=n['rows_settled_only'], settled_classes=n['settled_classes'], not_settled_classes=n['not_settled_classes'], other_classes=n['other_classes'])


def delta(a, b):
    return dict(settled=b['settled'] - a['settled'], not_settled=b['not_settled'] - a['not_settled'], other=b['other'] - a['other'], rows_settled_only=b['rows_settled_only'] - a['rows_settled_only'])


def so_rows_of(cmap_):
    rs = row_status(cmap_)
    return {r for r, t in rs.items() if t['N'] == 0 and t['O'] == 0 and t['U'] == 0 and t['S'] > 0}


N_B0 = snap()
CLS_AFTER_JOBS = dict(cls)

# ---- overlay A: HM-O withdrawn (ruling A). A credited key moves to CONDITIONAL_ON_BINDING iff its proving closure reaches a fresh external of a CROSS-CRATE Aspis item resolved by name to the gate constant.
#      Keys whose only by-name externals are unprefixed (own-crate / opaque) items are listed HMO_UNDETERMINED for the lead (the ruling names cross-crate items), not moved.
HMO_MOVE = []; HMO_OWN_ONLY = []
for k, v in sorted(HMO.items()):
    if v['verdict'] == 'HMO_YES':
        if 'cross_crate' in v['external_kinds']: HMO_MOVE.append(k)
        else: HMO_OWN_ONLY.append(k)
for k in HMO_OWN_ONLY:
    HMO[k]['verdict'] = 'HMO_UNDETERMINED'; HMO[k]['why'] = 'by-name externals are own-crate or unprefixed items only (%s); the ruling names cross-crate items; evidence decides the binding exists, not its class: for the lead' % ', '.join(HMO[k]['external_names'][:4])
    HMO[k]['subkind'] = 'OWN_CRATE_NAME_BINDING_ONLY'
for k in HMO_MOVE:
    assert cls[k] in SET
    cls[k] = 'CONDITIONAL_ON_BINDING'
N_A = snap()
rows_before_A = so_rows_of(CLS_AFTER_JOBS); rows_after_A = so_rows_of(cls)
ROW_LOSS_A = sorted(rows_before_A - rows_after_A)
print('overlay A (HM-O): moved %d keys; settled %d -> %d, other %d -> %d, rows %d -> %d; undetermined %d (of which own-crate-only %d)' % (
    len(HMO_MOVE), N_B0['settled'], N_A['settled'], N_B0['other'], N_A['other'], N_B0['rows_settled_only'], N_A['rows_settled_only'],
    sum(1 for v in HMO.values() if v['verdict'] == 'HMO_UNDETERMINED'), len(HMO_OWN_ONLY)))

# ---- overlay B: parse_blocks demotions (ruling B): credited key whose declaration the pre-fix generator dropped and that has no exit-0 theorem naming it -> OPEN
for k in DEMOTE:
    assert k in cls and kind(cls[k]) != 'N'
    cls[k] = 'OPEN'
N_B = snap()
print('overlay B (parse_blocks): demotions %d; -> %d/%d/%d rows %d' % (len(DEMOTE), N_B['settled'], N_B['not_settled'], N_B['other'], N_B['rows_settled_only']))
FINAL = N_B
assert FINAL['settled'] + FINAL['not_settled'] + FINAL['other'] == 1707

# ---- CANNOT_EXTRACT key set on the final map: the 65 keys of PCXN plus the PCWS_ keys of lead class CANNOT_EXTRACT (13: TerminalDecoder 10, DecodeKFullV10 3)
PCWS_ST = S('PCWS', 'prov-p5i-20261110', 'STATUS')
pcws_ce = sorted(x['module'] + '|' + x['definition'] for x in PCWS_ST['definitions'] if x['lead_class'] == 'CANNOT_EXTRACT')
CE_NEW = sorted(k for k in pcws_ce if k in cone and k not in CE_KEYS)
CE_KEYS2 = set(CE_KEYS) | {k for k in pcws_ce if k in cone}
OT_KEYS2 = [k for k in cone if cls[k] == 'OPEN_TRANSCRIPTION']
blk2 = dict(open_transcription_keys=blocked(OT_KEYS2, cls), open_transcription_item_keys=blocked(OT_ITEM_KEYS, cls),
            cannot_extract_pcxn_65=blocked(sorted(CE_KEYS), cls), cannot_extract_consolidated=blocked(sorted(CE_KEYS2), cls),
            union_ot_keys_and_ce=blocked(sorted(set(OT_KEYS2) | CE_KEYS2), cls))
for n_, b_ in blk2.items(): print('  ', n_.ljust(30), 'keys %d unsettled %d | rows touched %d alone %d among %d' % (b_['keys_in_set'], b_['keys_not_settled'], b_['rows_touched'], b_['blocked_alone'], b_['blocked_among_others']), b_['alone_rows'])
print('CE keys added by PCWS_:', len(CE_NEW), 'already in the PCXN set:', len(pcws_ce) - len(CE_NEW))


# =====================================================================================================================
# B5. citations (item C) joined to the key universe, outputs
# =====================================================================================================================
OUT = args.outdir
CIT = json.load(open(OUT + '/PCXO_CITATIONS.json'))
cit_keys = []
for r_ in CIT['records']:
    c = r_.get('comparison')
    if not c: continue
    for nm in sorted(set(c['differing_declarations']) | set(c['only_in_plan_source']) | set(c['only_in_cited_source'])):
        for k in keys_of(r_['module'], nm):
            cit_keys.append(dict(module=r_['module'], cited=r_.get('cited_path') or r_.get('cited_source_found'), declaration=nm,
                                 difference=('text differs' if nm in c['differing_declarations'] else 'only in plan source' if nm in c['only_in_plan_source'] else 'only in cited source'),
                                 key=k, class_final=cls.get(k)))
CIT_SUMMARY = dict(records=CIT['counts']['records'], by_status=CIT['counts']['by_status'], differing_declaration_entries=sum(len(r_['comparison']['differing_declarations']) + len(r_['comparison']['only_in_plan_source']) + len(r_['comparison']['only_in_cited_source']) for r_ in CIT['records'] if r_.get('comparison')),
                   entries_that_are_keys_of_the_1876_universe=len(cit_keys), credited_keys_among_them=sorted({x['key'] for x in cit_keys if x['class_final'] and kind(x['class_final']) != 'N'}), key_entries=cit_keys)
print('citations: %s; differing declaration entries %d, of which keys %d, credited %d' % (CIT['counts']['by_status'], CIT_SUMMARY['differing_declaration_entries'], len(cit_keys), len(CIT_SUMMARY['credited_keys_among_them'])))

head_end = subprocess.run(['git', 'rev-parse', args.ref], capture_output=True, check=True).stdout.decode().strip()
WT_HEAD = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, check=True).stdout.decode().strip()
per_class = dict(settled=FINAL['settled_classes'], not_settled=FINAL['not_settled_classes'], other=FINAL['other_classes'])
all_classes = collections.Counter(cls[k] for k in cone)
assert sum(all_classes.values()) == 1707

# ---- per-key attribution of every change since the reproduced PCXN map
chg = []
for k in cone:
    if CLS_PCXN[k] != cls[k]: chg.append(dict(key=k, pcxn=CLS_PCXN[k], now=cls[k]))
by_step = []
by_step.append(dict(step='PCXN reproduced (stage A)', **brief2(NUM_PCXN)))
for j_ in log[STAGE_B_LOG_START:]:
    by_step.append(dict(step='job %s (%s, %s)' % (j_['job'], j_['prefix'], j_['dir']), settled=j_['after']['settled'], not_settled=j_['after']['not_settled'], other=j_['after']['other'], rows_settled_only=j_['after']['rows_settled_only'], delta=j_['delta'],
                        records_mapped=j_['records_mapped'], changes=j_['changes'], changes_in_cone=j_['changes_in_cone'], notes=j_['notes'], mapping=j_['adapter_mapping']))
by_step.append(dict(step='overlay A: HM-O withdrawn', **brief2(N_A), delta=delta(N_B0, N_A)))
by_step.append(dict(step='overlay B: parse_blocks demotions', **brief2(N_B), delta=delta(N_A, N_B)))

row_lines = {n_: {k_: v_ for k_, v_ in b_.items() if k_ not in ('touched_rows',)} for n_, b_ in blk2.items()}
PCXN_blk = {n_: {k_: v_ for k_, v_ in b_.items() if k_ not in ('touched_rows',)} for n_, b_ in STAGE_A['counts']['blocking'].items()}
counts = dict(schema='PCXO_COUNTS/1', target_established=False, research_ref=REF, research_head_at_end=head_end, worktree_head_at_start='cfb57d20236', frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
              reproduction=dict(expected='1127/441/139, rows 122 (PCXN_COUNTS.json, committed)', got=dict(settled=NUM_PCXN['settled'], not_settled=NUM_PCXN['not_settled'], other=NUM_PCXN['other'], rows_settled_only=NUM_PCXN['rows_settled_only']),
                                status='REPRODUCED EXACTLY: headline, per-class and blocking lines asserted equal to the committed PCXN_COUNTS.json at the current research head; the unmodified PCXN_recount.py at its pin 6c8f7bb1b3d also gives 1127/441/139, rows 122'),
              merged_after_pcxn_pin=dict(pin='6c8f7bb1b3d', dirs=unchained_stageB + ['evidence/prov-p6k-20261110 (PCXN_ itself, no adapter)', 'evidence/prov-p6m-20261110 (PCXP_, audit only, no class map; 0 credited keys affected)']),
              chain=by_step,
              headline=dict(settled_of_1707=FINAL['settled'], not_settled_of_1707=FINAL['not_settled'], other_of_1707=FINAL['other'], rows_settled_only_of_599=FINAL['rows_settled_only'], per_class=per_class, all_classes=dict(sorted(all_classes.items()))),
              sensitivity=dict(if_own_crate_only_externals_also_moved=dict(moved=len(HMO_MOVE) + len(HMO_OWN_ONLY), settled=FINAL['settled'] - len(HMO_OWN_ONLY)),
                               hmo_undetermined_keys=sum(1 for v in HMO.values() if v['verdict'] == 'HMO_UNDETERMINED'),
                               note='HMO_UNDETERMINED keys stay in their class; if every one were HM-O the settled count would fall by at most that number'),
              overlay_A=dict(name='HM-O withdrawn as a trust row (Stream A lead ruling A)', moved_keys=len(HMO_MOVE), before=brief2(N_B0), after=brief2(N_A), delta=delta(N_B0, N_A), rows_lost=ROW_LOSS_A, rows_lost_count=len(ROW_LOSS_A)),
              overlay_B=dict(name='generator parse_blocks audit (ruling B)', demotions=len(DEMOTE), demoted_keys=DEMOTE, before=brief2(N_A), after=brief2(N_B), delta=delta(N_A, N_B)),
              blocking_final=row_lines, blocking_pcxn_reproduced=PCXN_blk,
              cannot_extract=dict(keys_pcxn=len(CE_KEYS), keys_final=len(CE_KEYS2), added_by_PCWS_in_cone=CE_NEW, pcws_ce_keys_total=len(pcws_ce), note='PCWS_ (P5i) lead class CANNOT_EXTRACT: AspisR1TerminalDecoder 10 keys, AspisR1DecodeKFullV10 3 keys; 6 of the 13 in the cone were already in the PCXN set (decode_k and the decode_pool_v1* name matches); PCWU_ adds no cone key (prepared_claim nested-loop returns: CE03 keys; stage1/stage2: no key)'),
              open_transcription=dict(keys=len(OT_KEYS2), keys_list=OT_KEYS2),
              changes_since_pcxn=chg, unmatched_stage_b=[u for u in unmatched if u.get('job') in ('PCWQ', 'PCWT', 'PCWS', 'PCWU')], conflicts_stage_b=[c_ for c_ in conflicts if c_.get('job') in ('PCWQ', 'PCWT', 'PCWS', 'PCWU')],
              hmo_summary=dict(credited_keys_evaluated=len(HMO), verdicts=dict(collections.Counter(v['verdict'] for v in HMO.values())), moved=len(HMO_MOVE), own_crate_only_listed_undetermined=len(HMO_OWN_ONLY)),
              parse_blocks_summary=dict(demotions=len(DEMOTE), pairs=len(PAIRS), gate_rows=len(AUDIT_ROWS), gate_rows_with_a_drop=sum(1 for r_ in AUDIT_ROWS if r_['dropped']), dropped_declarations=len(PB), dropped_that_are_keys=len(PB_KEYS), credited_keys_among_them=len({x['key'] for x in PB if x['credited']})),
              citations=CIT_SUMMARY)
json.dump(counts, open(OUT + '/PCXO_COUNTS.json', 'w'), indent=1); open(OUT + '/PCXO_COUNTS.json', 'a').write('\n')

# ---- PCXO_HMO.json
mod_tab = collections.defaultdict(lambda: dict(credited_keys=0, moved=0, undetermined=0, no=0, externals=collections.Counter(), classes=collections.Counter()))
for k, v in HMO.items():
    t = mod_tab[k.split('|')[0]]; t['credited_keys'] += 1
    if k in set(HMO_MOVE):
        t['moved'] += 1; t['classes'][v['class_before']] += 1
        for n in v['external_names']:
            if ext_kind(n) == 'cross_crate': t['externals'][n] += 1
    elif v['verdict'] == 'HMO_UNDETERMINED': t['undetermined'] += 1
    else: t['no'] += 1
table = [dict(module=m_, credited_keys=t['credited_keys'], moved_to_CONDITIONAL_ON_BINDING=t['moved'], undetermined=t['undetermined'], no_external_binding=t['no'], class_before_of_moved=dict(t['classes']), cross_crate_externals_of_moved=dict(t['externals'].most_common())) for m_, t in sorted(mod_tab.items(), key=lambda kv: (-kv[1]['moved'], kv[0])) if t['moved'] or t['undetermined']]
ext_queue = collections.Counter()
for k in HMO_MOVE:
    for n in HMO[k]['external_names']:
        if ext_kind(n) == 'cross_crate': ext_queue[n] += 1
hmo_out = dict(schema='PCXO_HMO/1', target_established=False, research_ref=REF,
               ruling='Stream A lead 2026-11-10 (A): CrossCrateConstantEncoding (PROPOSED-HM-O) withdrawn as a trust row; every credited key whose proof relies on a fresh Aeneas EXTERNAL for a cross-crate Aspis item resolved BY NAME to the gate constant, rather than an emission that includes the item as a definition, becomes CONDITIONAL_ON_BINDING; where the evidence cannot decide: HMO_UNDETERMINED (no guess).',
               method=['credited keys = cone keys whose class on the map after the stage B jobs is a settled class (%d)' % len(HMO),
                       'crediting job per key: the job adapter that last set a settled class (this run), else the PCXD_PROVENANCE record (proving_file directory, receipt directory, decided_by job), else the baseline class EQUALITY_PROVED_P1N (job P1n); keys credited by RECEIPTED_PIN_EQUAL / RECEIPTED_SELECTED_MASK_PROBE have no fresh = gate theorem as credit basis and are HMO_UNDETERMINED unless an exit-0 proof of the crediting job exists',
                       'proof evidence: (1) an exit-0 standard-axioms theorem of the crediting job whose statement right-hand side is the key (indexed from every PRVEq file; names completed by the enclosing namespace), else (2) a PRVEq file of that job that imports the gate module and has a fresh declaration of the key name; never another job\'s proof of the same definition',
                       'externals of the fresh emission: the external_funs of the generator report whose fresh_namespace equals the proving file\'s (union over reports of that namespace); for a file not produced by a generator report: the names of known external functions/constants (all report external_funs plus PCXD_EXTERNALS) that the fresh namespace does not declare',
                       'closure: the fresh declaration of the key and, transitively, every declaration of the same fresh namespace it references (a declaration of the fresh namespace takes priority over an opened gate name, as in Lean name resolution; so an item emitted as a definition, e.g. with --include, is NOT an external)',
                       'an external counts as an Aspis item unless PCXD_EXTERNALS classes it as an SDK/core/alloc/slice-iterator/option/array/num model (HM-A..HM-F rows) or, if unlisted, its name starts with core./alloc./std./solana_/Slice./Array./MutAArray; it is cross-crate if it starts with aspis_ or fast_pairing.',
                       'type keys (Types modules, .equiv theorems) are HMO_NO by kind (a type declaration has no function or constant external)'],
               rule_applied='moved = credited key with at least one CROSS-CRATE Aspis-item external in its proving closure; keys whose only by-name externals are unprefixed (own-crate or opaque) items are listed HMO_UNDETERMINED with subkind OWN_CRATE_NAME_BINDING_ONLY (the ruling names cross-crate items; the evidence shows a by-name binding exists): the lead may move them (sensitivity in PCXO_COUNTS.json)',
               limitations=['the externals come from generator reports and from a free-name scan, not from a re-extraction; a key whose proving file is a hand-adapted copy of the emission is evaluated on that file',
                            'a key proved through a PRVC loop-bridge controller whose statement is not of the form `@fresh = @gate` has no statement-level theorem: evaluated through (2) or HMO_UNDETERMINED',
                            'a key credited by receipt of a text equality is not evaluated (no external list per key is recorded); it is HMO_UNDETERMINED, not cleared',
                            'class labels of stage A were not changed by this overlay except the moved keys'],
               counts=dict(credited_keys=len(HMO), verdicts=dict(collections.Counter(v['verdict'] for v in HMO.values())), moved=len(HMO_MOVE), by_class_before=dict(collections.Counter(HMO[k]['class_before'] for k in HMO_MOVE)),
                           undetermined_by_class=dict(collections.Counter(v['class_before'] for v in HMO.values() if v['verdict'] == 'HMO_UNDETERMINED')), own_crate_only=len(HMO_OWN_ONLY)),
               discharge_queue_by_module=table, discharge_queue_by_external=[dict(external=n, moved_keys=c) for n, c in ext_queue.most_common()],
               moved_keys=[dict(key=k, class_before=HMO[k]['class_before'], externals=HMO[k]['external_names'], proof=[(c['theorem'], c['file']) for c in HMO[k]['candidates'] if c.get('evaluable') and c['aspis_item_externals']][:2]) for k in HMO_MOVE],
               undetermined_keys=[dict(key=k, class_before=v['class_before'], why=v['why'], subkind=v.get('subkind'), job_status_hint=v.get('status_hint')) for k, v in sorted(HMO.items()) if v['verdict'] == 'HMO_UNDETERMINED'],
               no_binding_keys=[dict(key=k, class_before=v['class_before'], subkind=v.get('subkind'), proof=[(c['theorem'], c['file']) for c in v['candidates'] if c.get('evaluable')][:1]) for k, v in sorted(HMO.items()) if v['verdict'] == 'HMO_NO'])
json.dump(hmo_out, open(OUT + '/PCXO_HMO.json', 'w'), indent=1); open(OUT + '/PCXO_HMO.json', 'a').write('\n')

# ---- PCXO_PARSE_BLOCKS_AUDIT.json
pre_fix = sorted(f for f, v in GEN_VARIANT.items() if v != 'C')
audit_out = dict(schema='PCXO_PARSE_BLOCKS_AUDIT/1', target_established=False, research_ref=REF,
                 defect='parse_blocks of the *_gen_equalities.py lineage did not recognise a declaration that follows import lines (variant B) or any header line (variant A) with no blank line between: the raw block was classed `other`, so the first declaration of the gate (or fresh) text produced no equality',
                 fix=dict(file=FIX_FILE, sha256=GEN_SHA[FIX_FILE], source='PCWP_TOOLS.json: "parse_blocks peels leading import lines"', also_fixed_in=[f for f, v in GEN_VARIANT.items() if v == 'C' and f != FIX_FILE]),
                 generator_variants={f: dict(variant=v, sha256=GEN_SHA[f]) for f, v in sorted(GEN_VARIANT.items())},
                 finding_unfixed_descendants=[f for f in GEN_VARIANT if GEN_VARIANT[f] == 'B' and f.split('/')[1] in ('prov-p5h-20261110', 'prov-p5i-20261110', 'prov-p7a-20261110')],
                 finding_note='PCWR_ (P5h), PCWS_ (P5i) and PCWT_ (P7a) generators carry the PCWJ_ parse_blocks WITHOUT the import fix (variant B); the fix is only in PCWP_ and PCWW_',
                 method=['all PRVEq_*.lean files with the header "GENERATED by <gen> for gate module <M>" give the (generator, module) pairs (%d pairs; PRVEq_bundle_* compile vehicles are concatenations of member files and are skipped)' % len(PAIRS),
                         'gate source per pair: the saved generator input copy (gate_<M>.lean) in the job directory of the pair, else any saved copy of that module, else the l187_plan.json source (PCXO_PLAN_ENTRIES.json); %d of %d rows use the plan source' % (sum(1 for r_ in AUDIT_ROWS if r_.get('source_is_l187_plan')), len(AUDIT_ROWS)),
                         'dropped = declarations recognised by the fixed parse (variant C) but not by the generator\'s own variant (A: no peeling; B: peeling without import)',
                         'a dropped declaration maps to a key when the module matches (dots and underscores ignored) and the definition name ends with the declaration name',
                         'credited = class on the final map is a settled or other class; theorem found = an exit-0 standard-axioms theorem (receipt.json print_axioms of an exit-0 lean scope) recorded for the key, or one whose statement right-hand side is the key',
                         'fresh side: every Funs.lean/Types.lean under evidence/prov-p* parsed with the variant of its job directory (informational and applied by name)'],
                 counts=dict(generators=len(GEN_VARIANT), pre_fix_generators=len(pre_fix), pairs=len(PAIRS), gate_rows=len(AUDIT_ROWS), gate_rows_with_a_drop=sum(1 for r_ in AUDIT_ROWS if r_['dropped']), fresh_files_with_a_drop=len(FRESH_ROWS),
                             dropped_declarations=len(PB), dropped_that_are_keys=len(PB_KEYS), credited_keys_among_them=len({x['key'] for x in PB if x['credited']}), demotions=len(DEMOTE), pairs_without_any_gate_source=len(NO_GATE_SOURCE)),
                 pre_fix_generators=pre_fix, demoted_keys=DEMOTE,
                 rows=[dict(module=x['module'], side=x['side'], generator=x['generator'], variant=x['variant'], dropped_declaration=x['dropped_declaration'], first_line=x['first_line'], source=x['source'], key=x['key'], class_now=x['class_now'],
                            credited=x['credited'], theorem_found=x['theorem_found'], theorems=(x.get('recorded_theorems', []) + x.get('statement_theorems', []))[:4] if x['key'] else [], action=x['action']) for x in PB],
                 gate_sources_without_a_drop=len([r_ for r_ in AUDIT_ROWS if not r_['dropped']]), no_gate_source=NO_GATE_SOURCE)
json.dump(audit_out, open(OUT + '/PCXO_PARSE_BLOCKS_AUDIT.json', 'w'), indent=1); open(OUT + '/PCXO_PARSE_BLOCKS_AUDIT.json', 'a').write('\n')
print('written: PCXO_COUNTS.json PCXO_HMO.json PCXO_PARSE_BLOCKS_AUDIT.json; research head at end', head_end[:12], 'unchanged' if head_end == REF else 'MOVED since the start of the run')
print('FINAL (PCXO) settled %d not settled %d other %d rows %d' % (FINAL['settled'], FINAL['not_settled'], FINAL['other'], FINAL['rows_settled_only']))
print('per class', json.dumps(per_class))


# ---- PCXO_TOOLS.json and PCXO_REPORT.md (numbers from this run)
def num(n): return '%d/%d/%d' % (n['settled'], n['not_settled'], n['other'])
tools = dict(schema='PCXO_TOOLS/1', target_established=False, lean=0, extraction=0, host_scopes=0, python='python3 -I, stdlib only',
             scripts=[dict(file='evidence/prov-p6l-20261110/PCXO_recount.py', base='evidence/prov-p6k-20261110/PCXN_recount.py (copied; stage A reproduces it; stage B added)', run='python3 -I evidence/prov-p6l-20261110/PCXO_recount.py (from the worktree root; reads research pinned to one commit at start; about 30 s)',
                           changes_vs_PCXN=['stage A: ref read at the current research head; the unchained-dir assert now lists the dirs merged since the PCXN pin (P5f..P8a, P6k, P6m); PCXN outputs are compared in memory with the committed PCXN_COUNTS.json (headline and blocking lines)',
                                            'adapters in merge order for P5g PCWQ_ (lead_classes), P7a PCWT_ (lead_class per record), P5i PCWS_ (lead_class per definition), P8a PCWU_ (credited records, Equiv as TYPE_ISOMORPHISM); P5j PCWV_, P5k PCWW_, P5l PCWX_ paused with no credit (no-op adapters); P6k and P6m: no class map',
                                            'overlay A (HM-O) over the fresh emissions\' external_funs, per credited key; overlay B (parse_blocks) over all gate (and fresh) texts of every generator variant',
                                            'blocking lines recomputed on the final map; CE key set extended by the PCWS_ CANNOT_EXTRACT keys in the cone'],
                           reads=['git show <pinned research commit>:<path> through one persistent git cat-file --batch process', 'evidence/prov-p6l-20261110/PCXO_PLAN_ENTRIES.json (cached module entries of l187_plan.json)']),
                      dict(file='evidence/prov-p6l-20261110/PCXO_citations.py', run='python3 -I evidence/prov-p6l-20261110/PCXO_citations.py [--fetch]', ssh='--fetch: one read-only ssh to dombarker@100.108.41.90, a short python script reading /home/dombarker/project-offloads/codex-cx-replay-l187-20261109/l187_plan.json and printing the module -> source path/sha entries of the listed modules; the plan file is not copied; no host scope, nothing written on the host'),
                      ],
             generator_fix=dict(file=FIX_FILE, sha256=GEN_SHA[FIX_FILE], note='PCWP_ (P5f) parse_blocks import-line peel; also in PCWW_ (P5k); not in PCWR_, PCWS_, PCWT_'),
             research_ref=REF, outputs=['PCXO_COUNTS.json', 'PCXO_HMO.json', 'PCXO_PARSE_BLOCKS_AUDIT.json', 'PCXO_CITATIONS.json', 'PCXO_PLAN_ENTRIES.json', 'PCXO_REPORT.md', 'PCXO_TOOLS.json'])
json.dump(tools, open(OUT + '/PCXO_TOOLS.json', 'w'), indent=1); open(OUT + '/PCXO_TOOLS.json', 'a').write('\n')

jobs_line = '; '.join('%s %s %s' % (st_['step'].split(' ')[1], num(st_), ('rows %d' % st_['rows_settled_only'])) for st_ in by_step[1:5])
ot_b = blk2['open_transcription_keys']; oti_b = blk2['open_transcription_item_keys']; ce_b = blk2['cannot_extract_consolidated']
sc = per_class['settled']; nsc = per_class['not_settled']; oc_ = per_class['other']
fmt = lambda d: ', '.join('%s %d' % (k_, v_) for k_, v_ in d.items())
top_mod = ', '.join('%s %d' % (t_['module'], t_['moved_to_CONDITIONAL_ON_BINDING']) for t_ in table[:6])
n_cit_diff = CIT_SUMMARY['differing_declaration_entries']
report = f"""# PCXO_ (P6l): recount v3, HM-O withdrawal, parse_blocks audit, citation re-points

**Result: settled {FINAL['settled']} / not settled {FINAL['not_settled']} / other {FINAL['other']} of 1707; rows settled-only {FINAL['rows_settled_only']} of 599.**
- Settled: {fmt(sc)}.
- Not settled: {fmt(nsc)}.
- Other: {fmt(oc_)}.

**Reproduction first.** The PCXN_ chain is reproduced exactly (asserted against the committed PCXN_COUNTS.json): 1127 / 441 / 139, rows 122, with the same OPEN_TRANSCRIPTION and CANNOT_EXTRACT lines. Script work on the Mac, 0 Lean, 0 extraction, 0 host scopes; reads research {REF[:12]}.

**Jobs merged after the PCXN pin, in merge order** (stage, settled/not settled/other, rows): {jobs_line}. P5g, P7a and P5i apply their lead_classes / lead_class (P5g: putK equal, 23 conditional on binding; P7a: 2 equalities, 12 library-row, 34 conditional; P5i: 4 NJS OFF-emission equalities, 10 conditional, 1 library-row, 3 type isomorphisms, 13 CANNOT_EXTRACT). P8a (PCWU_) has no lead_classes: its four credited records are applied as given. P5j, P5k, P5l are paused with no credit; P6m (PCXP_) is an audit with 0 credited keys affected. Every change is listed per key in PCXO_COUNTS.json.

**Overlay A, HM-O withdrawn.** {len(HMO_MOVE)} credited keys move from settled to CONDITIONAL_ON_BINDING (settled -{len(HMO_MOVE)}, other +{len(HMO_MOVE)}, rows -{len(ROW_LOSS_A)}). Rule: the proving closure of the key, in the file of the job that credited it, reaches a fresh Aeneas external of a cross-crate Aspis item (aspis_core, aspis_statement) that resolves by name to the gate constant, and the emission does not carry the item as a definition. The queue by module (PCXO_HMO.json has all of it): {top_mod}. {len(HMO)-len(HMO_MOVE)-sum(1 for v in HMO.values() if v['verdict']=='HMO_UNDETERMINED')} keys are cleared (no such external); {sum(1 for v in HMO.values() if v['verdict']=='HMO_UNDETERMINED')} are HMO_UNDETERMINED, not cleared: {sum(1 for v in HMO.values() if v['verdict']=='HMO_UNDETERMINED' and v.get('evidence_basis')=='NO_CREDITING_JOB')} credited by receipt of a text equality or without a recorded proving job, the rest with no recorded proof of the crediting job that the scan can read, {len(HMO_OWN_ONLY)} with by-name externals that are own-crate items only (moving them would give {FINAL['settled']-len(HMO_OWN_ONLY)} settled). The externals come from generator reports and a free-name scan, not from re-extraction.

**Overlay B, generator parse_blocks audit.** Demotions: {len(DEMOTE)}. Fixed generator PCWP_gen_equalities.py, sha256 {GEN_SHA[FIX_FILE]}. {audit_out['counts']['pairs']} (generator, module) pairs checked against saved gate sources ({sum(1 for r_ in AUDIT_ROWS if r_.get('source_is_l187_plan'))} rows use the l187 plan source); {audit_out['counts']['gate_rows_with_a_drop']} gate rows drop a declaration, {len(PB_KEYS)} dropped declarations are keys, {len({x['key'] for x in PB if x['credited']})} are credited, and each of those has an exit-0 standard-axioms theorem naming it (PCXO_PARSE_BLOCKS_AUDIT.json). Finding: PCWR_, PCWS_ and PCWT_ generators still carry the unfixed parse_blocks (only PCWP_ and PCWW_ have the fix).

**Blocking lines on the final map.** OPEN_TRANSCRIPTION keys ({ot_b['keys_in_set']}): rows alone {ot_b['blocked_alone']}, among other blockers {ot_b['blocked_among_others']} ({oti_b['keys_in_set']} item-mapped keys: alone {oti_b['blocked_alone']}, among {oti_b['blocked_among_others']}). CANNOT_EXTRACT ({ce_b['keys_in_set']} keys, {len(CE_NEW)} added by P5i): rows alone {ce_b['blocked_alone']} ({', '.join(ce_b['alone_rows'])}), among {ce_b['blocked_among_others']} ({ce_b['rows_touched']} touched); PCXN_ had alone 6, among 123 before overlay A.

**Citations (item C).** The 18 source-citation differences are re-pointed to the l187_plan.json source ({len(PLAN_ENTRIES['entries'])} module entries read by one read-only ssh): 4 are the sha256 of a proving file, not a gate source (all {sum(r_['proving_file_check']['equality_theorems'] for r_ in CIT['records'] if r_.get('proving_file_check'))} theorem right-hand sides resolve to plan-source declarations); 14 compare generator-input or path copies with the plan source and differ in {n_cit_diff} declaration entries, {len(cit_keys)} of them keys and {len(CIT_SUMMARY['credited_keys_among_them'])} credited keys (PCXO_CITATIONS.json). These are citation differences against an older copy, not proof errors: the theorems state against compiled gate constants.

Target not yet established.
"""
open(OUT + '/PCXO_REPORT.md', 'w').write(report)
print('report words', len(report.split()))
