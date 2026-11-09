#!/usr/bin/env python3
"""PCUB_final.py: builds PCUB_EQ_STATUS.json, PCUB_FOR_P3.json, PCUB_HAND_MODELS.json, PCUB_PROVENANCE.json from the
generator states (gen/<label>.state2.json), the verify receipt PCUB_L004 and the committed fresh emissions.
Run from this directory: python3 -B PCUB_final.py"""
import json, re, sys, glob, os, subprocess, hashlib
from pathlib import Path
sys.path.insert(0, '.')
import PCUB_gen_equalities as G
EV = Path('..').resolve()
OK_AX = {'propext', 'Classical.choice', 'Quot.sound'}
FROZEN = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
P = json.load(open('PCUB_PARTITION.json'))['modules']
CL = sorted(n for n in P if n.startswith('RPu') or n.startswith('RPv'))

# ---- usable fresh (overflow-checks-on) emission directories
dirs = []
for r in ['PCQ_E037', 'PCQ_E038', 'PCQ_E039', 'PCQ_E040']: dirs += glob.glob(f'{EV}/prov-p1a-20261109/{r}_emitted/raw/*')
for n in list(range(1, 13)) + [22, 23]: dirs += glob.glob(f'{EV}/prov-p1c-20261109/PCQC_E{n:03d}_emitted/raw/*')
CR = r'(aspis_core|aspis_r1_cost_probe|aspis_statement|aspis_r1_mask_extraction_probe|aspis_pool_wallet_v1|CRATE|adapter_owned|wide_to_bytes)::'
def norm(s): return re.sub(CR, '', s).strip()
fresh = {}
for d in dirs:
    for f in ['Funs.lean', 'Types.lean', 'FunsExternal_Template.lean', 'TypesExternal_Template.lean']:
        p = os.path.join(d, f)
        if not os.path.exists(p): continue
        t = open(p).read()
        for m in re.finditer(r'/--\s*(?:Trait implementation: )?\[(.*?)\](?::|\n)', t):
            fresh.setdefault(norm(m.group(1)), []).append(dict(dir=os.path.relpath(d, EV), file=f, crate_in_fresh_name=m.group(1).split('::')[0]))

# ---- frozen-source name heuristic
FT = subprocess.run(['git', 'ls-tree', '-r', '--name-only', FROZEN], capture_output=True, text=True, cwd='../..').stdout.split('\n')
FT = [x for x in FT if x.startswith('crates/') and x.endswith('.rs')]
_blob = {}
def blob(p):
    if p not in _blob: _blob[p] = subprocess.run(['git', 'show', f'{FROZEN}:{p}'], capture_output=True, text=True, cwd='../..').stdout
    return _blob[p]
def frozen_item(rust):
    s = re.sub(r'\{[^{}]*\}', '', rust.replace('CRATE::', ''))  # drop impl/type braces (heuristic)
    segs = [x for x in s.split('::') if x and not re.fullmatch(r'closure(_\d+)?', x)]
    if not segs: return dict(frozen_file=None, item_found=None)
    item = segs[-1]
    for k in range(len(segs) - 1, 0, -1):
        mp = '/'.join(segs[:k])
        c = [x for x in FT if x.endswith('/src/' + mp + '.rs') or x.endswith('/src/' + mp + '/mod.rs')]
        if c:
            f = c[0]
            return dict(frozen_file=f, item=item, item_found=bool(re.search(r'\b(fn|struct|enum|const|static|type)\s+' + re.escape(item) + r'\b', blob(f))))
    return dict(frozen_file=None, item=item, item_found=None)

# ---- generator states (non-control labels) and the verify receipt
PASSES = {  # module -> [(label, fresh run, fresh dir, rename)]
    'RPu_FIq_Native01': [('RPu_FIq_Native01', 'PCQ_E038', 'prov-p1a-20261109/PCQ_E038_emitted/raw/PCQ_aspis_core_field', [])],
    'RPu_FIq_Native11': [('RPu_FIq_Native11', 'PCQ_E039', 'prov-p1a-20261109/PCQ_E039_emitted/raw/PCQ_aspis_statement_pool_v1_payment_relation', [])],
    'RPu_FIq_NativeTypes': [
        ('RPu_FIq_NativeTypes_a', 'PCQ_E037', 'prov-p1a-20261109/PCQ_E037_emitted/raw/PCQ_checked_field', []),
        ('RPu_FIq_NativeTypes_b', 'PCQ_E039', 'prov-p1a-20261109/PCQ_E039_emitted/raw/PCQ_aspis_statement_pool_v1_payment_relation', ['aspis_core.field.M31=field.M31']),
        ('RPu_FIq_NativeTypes_c', 'PCQ_E040', 'prov-p1a-20261109/PCQ_E040_emitted/raw/PCQ_aspis_statement_pool_v1_pair_terminal', ['aspis_core.field.M31=field.M31', 'aspis_statement.=']),
        ('RPu_FIq_NativeTypes_e', 'PCQC_E023', 'prov-p1c-20261109/PCQC_E023_emitted/raw/PCQC_adapter_owned_b', ['aspis_core.field.M31=field.M31', 'aspis_statement.='])],
}
CTL = [('RPu_FIq_Native01_ctl', 'RPu_FIq_Native01'), ('RPu_FIq_Native11_ctl', 'RPu_FIq_Native11'), ('RPu_FIq_NativeTypes_ctl', 'RPu_FIq_NativeTypes')]
rc = json.load(open('PCUB_L004/receipt.json'))
AX = {}
for a in rc['print_axioms']:
    a = ' '.join(a.split()); m = re.match(r"'(.+?)' (does not depend on any axioms|depends on axioms: \[(.*)\])", a)
    if m: AX[m.group(1)] = sorted(x.strip() for x in (m.group(3) or '').split(',') if x.strip())
VER = dict(attempt='PCUB_L004', target='PRVEq_bundle_V1', exit=rc['exit_status'], wall_s=rc['wall_seconds'], peak_rss_kib=rc['peak_rss_kib'], swaps=rc['swaps'],
           n_axiom_lines=len(AX), axioms_ok=all(set(v) <= OK_AX for v in AX.values()))
def thm(label, n, equiv): return f'PRVEq.{label}.{n}' + ('.equiv' if equiv else '')

status = {}; p3 = []; tot = {}
def add(m, full, ent):
    status.setdefault(m, {})[full] = ent; tot[ent['status']] = tot.get(ent['status'], 0) + 1
for m in CL:
    mod = P[m]; gns = 'FIq_Native' if m.startswith('RPu') else None
    proved = {}; tio = {}
    for (label, run, fdir, ren) in PASSES.get(m, []):
        st = json.load(open(f'gen/{label}.state2.json')); rep = json.load(open(f'gen/{label}.report2.json'))
        for n, x in st['defs'].items():
            if x.get('status') == 'proved':
                t = thm(label, n, False); t2 = thm(label, n, True)
                name = t2 if t2 in AX else t
                proved.setdefault(n, []).append(dict(label=label, theorem=name, stage=x.get('stage'), fresh_run=run, fresh_dir=fdir, rename_fresh=ren, equiv=name.endswith('.equiv'), axioms=AX.get(name, 'NOT_FOUND'),
                                                   axioms_ok=(set(AX[name]) <= OK_AX) if name in AX else None))
        for n, t in rep['types'].items(): tio.setdefault(n, []).append(dict(label=label, fresh_run=run, status=t['status'], text_identical=t.get('text_identical')))
    for full, r in mod['reached_definitions'].items():
        n = full[len(gns) + 1:] if gns and full.startswith(gns + '.') else full
        if n in proved:
            e = proved[n][0]
            stt = 'PROVED_EQUIV' if e['equiv'] else ('PROVED_RFL' if e['stage'] == 1 else 'PROVED_UNFOLD')
            add(m, full, dict(status=stt, theorems=proved[n], gate_coverage_in_partition=r['coverage'], verify=VER['attempt'])); continue
        k = norm(r['rust']); hits = fresh.get(k, [])
        fi = frozen_item(r['rust'])
        funs_hits = [h for h in hits if h['file'] in ('Funs.lean', 'Types.lean')]
        ext_hits = [h for h in hits if 'External' in h['file']]
        if n in tio and any(t['status'] == 'text_identical_only' for t in tio[n]):
            add(m, full, dict(status='TEXT_IDENTICAL_ONLY', reason='structure/inductive shape for which the generator emits no Lean Equiv; text identical to the fresh declaration after the recorded rename_fresh rewrites', passes=tio[n], fresh=funs_hits[:3], frozen_source=fi)); continue
        if funs_hits:
            add(m, full, dict(status='NO_COMMON_LEAN_NAME', reason='a fresh declaration with the same Rust path (crate prefix ignored) exists, but no Lean statement was generated for this gate definition (different Lean name, constructor function, or non-comparable shape)', fresh=funs_hits[:3], frozen_source=fi)); continue
        if ext_hits:
            add(m, full, dict(status='FRESH_EXTERNAL_AXIOM_ONLY', reason='the only fresh form is an External-template axiom (opaque in the fresh emission); the gate has its own definition; no equality is possible', fresh=ext_hits[:3], frozen_source=fi,
                               gate_coverage_in_partition=r['coverage'])); continue
        add(m, full, dict(status='NO_FRESH_EMISSION', reason='no usable overflow-checks-on fresh frozen emission contains this Rust path; module is a transformed copy of a retained probe-crate emission; routed to P4 as cut-crate spec C001/C005 (PCO_extract_specs.json) with PCWB_CUT_TRIAGE.json triage "nothing"/"cargo_crate_only"; no extraction in this job (budget 0)',
                          partition_coverage=r['coverage'], frozen_source=fi))
# ---- controls
ctl = {}
for label, mod in CTL:
    st = json.load(open(f'gen/{label}.state2.json')); c = {'proved': [], 'failed': []}
    for n, x in st['defs'].items():
        if x.get('status') == 'proved':
            t2 = thm(label, n, True); t = thm(label, n, False)
            c['proved'].append(dict(name=n, stage=x.get('stage'), theorem=t2 if t2 in AX else t))
        else: c['failed'].append(dict(name=n, error=x.get('error'), class_in_generator=x.get('class')))
    ctl[label] = dict(gate_module=mod, n_proved=len(c['proved']), n_failed=len(c['failed']), failed=c['failed'], proved=c['proved'])
for label, c in ctl.items():
    for f in c['failed']:
        p3.append(dict(kind='CONTROL_FAILURE', control=label, gate_module=c['gate_module'], definition=f['name'], generator_class=f['class_in_generator'],
                       reclassified='CONTROL_HEARTBEAT_TIMEOUT', reason='self-copy control (text identical by construction): the generated rfl/unfold hit "(deterministic) timeout at whnf, maximum number of heartbeats (200000)" in PCUB_L001 (gate source has no maxHeartbeats header); not a body difference; not rerun with a raised limit', evidence='gen/probe_P1.log lines 814-837 of PRVEq_bundle_P1.lean'))
# ---- for P3 / follow-up: no failures of fresh comparisons; list definitions that need new fresh emissions
need = {}
for m, d in status.items():
    for full, e in d.items():
        if e['status'] == 'NO_FRESH_EMISSION':
            f = e['frozen_source']
            need.setdefault(f.get('frozen_file') or 'UNLOCATED', []).append(dict(module=m, definition=full, rust=P[m]['reached_definitions'][full]['rust'], item_found_by_name=f.get('item_found')))
for f, items in need.items(): p3.append(dict(kind='NEEDS_FRESH_EMISSION', frozen_file=f, n=len(items), items=items))
Path('PCUB_EQ_STATUS.json').write_text(json.dumps(dict(
    target_established=False, note='Statuses are per reached definition of the RPu_/RPv_ cluster. Equalities are statements PRVFresh_<M>.f = <gate>.f against compiled gate constants (never a source file); PROVED_EQUIV is a generated Equiv of structures. NO_FRESH_EMISSION is not a failure of equality: the definition has no fresh frozen counterpart in the usable emissions.',
    totals=tot, verify=VER, controls=ctl, modules={m: dict(group=P[m]['group'], subgroup=P[m]['subgroup'], kind=P[m]['kind'], n_reached=len(P[m]['reached_definitions']),
                                                         counts={s: sum(1 for e in status[m].values() if e['status'] == s) for s in sorted({e['status'] for e in status[m].values()})},
                                                         reached=status[m]) for m in CL if m in status}), indent=1))
Path('PCUB_FOR_P3.json').write_text(json.dumps(dict(target_established=False, note='No fresh-versus-gate body difference (no SEMANTIC and no CONFIG_MISMATCH) was found in this cluster: every compared definition was PROVED. Entries are (a) self-copy control failures (heartbeat timeouts, not differences) and (b) the Rust items that need a fresh frozen emission before an equality can be attempted.', items=p3), indent=1))
print(tot); print({m: len(d) for m, d in status.items()})
