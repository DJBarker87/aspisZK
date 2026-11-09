#!/usr/bin/env python3
"""Writes PCQG_FAILURES.json, PCQG_TOOLS.json, PCQG_CONFIG_BY_MODULE.json (reused P1e classification + NDE rows),
annotates each PINS with p1f_config, and writes PCQG_RECEIPT_SUMMARY.json. Derived from PCQF_records.py."""
import json,re,lzma,hashlib,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
def J(p):return json.loads(Path(p).read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
runs=[]
for f in sorted(E.glob('PCQG_E[0-9][0-9][0-9]_spec.json')):
    s=J(f);run=s['run'];rc=E/run/'receipt.json'
    if not rc.exists():continue
    runs.append((s,J(rc)))
def log(run):
    return lzma.decompress((E/run/'stdout.log.xz').read_bytes()).decode('utf8','replace') if (E/run/'stdout.log.xz').exists() else (E/run/'stdout.log').read_text()
def err(run):
    t=log(run)
    if 'ERROR Code failed to compile' in t:return 'Charon: "ERROR Code failed to compile" (charon-driver exit 101)'
    m=re.search(r'Uncaught exception:\s*\n(.*?)\n\nRaised',t,re.S) or re.search(r'Uncaught exception:\s*\n(.*?)(?:\nRaised|\nCalled)',t,re.S)
    body=re.sub(r'\s+',' ',m.group(1)).strip()[:480] if m else 'see stdout.log.xz'
    ml=re.search(r'Raised at ([^\n]+)',t)
    return 'Aeneas: '+body+((' | raised '+ml.group(1)[:80]) if ml else '')
def feats(c):return c['features'] if len(c['features'])<40 else 'audit feature set FS (see spec)'
fails=[]
for s,r in runs:
    if r['exit_status']!=0:
        c=s['configuration']
        fails.append(dict(run=s['run'],spec=s['spec_id'],label=s['label'],start_from=c['start_from'],include=c.get('include',[]),opaque=c.get('opaque',[]),features=feats(c),exit=r['exit_status'],wall_seconds=round(r['wall_seconds'],1),peak_rss_kib=r['peak_rss_kib'],cgroup_peak_bytes=r.get('cgroup_memory_peak_bytes'),error=err(s['run'])))
(E/'PCQG_FAILURES.json').write_text(json.dumps(dict(schema=1,target_established=False,note='Exact tool errors of P1f runs with the rebuilt ORIGINAL Aeneas. A shape that failed twice is retired; no failed shape was rerun unchanged.',failures=fails),indent=1)+'\n')
p0=None
for s,r in runs:
    pf=E/(s['run']+'_emitted')/(s['run']+'_PINS.json')
    if pf.exists() and s['spec_id'].startswith('NEW'):p0=J(pf);break
cfg=J(E/'PCQG_CONFIG_BY_MODULE_from_P1e.json')
cfg['modules'].update({'NDE_Reference2':dict(gate_file='evidence/native-front2-20261028/NDE_Reference2/Funs.lean',overflow_checks='ON',basis='PCVA_CLASSIFICATION CONFIG_MISMATCH: compiled gate is checked (x >>> 31#u32, i + i1, x3 - c); source uses plain operators'),
  'NDE_Reference5':dict(gate_file='evidence/native-front2-20261028/NDE_Reference5/Funs.lean',overflow_checks='ON',basis='PCVA_CLASSIFICATION CONFIG_MISMATCH: compiled gate has checked `index >>> level` and `1#u32 - i2`; source uses plain operators')})
cfg['ruling']=cfg.get('ruling','')+' | reused unchanged for P1f (PCQG_CONFIG_BY_MODULE_from_P1e.json) plus the two NDE modules'
(E/'PCQG_CONFIG_BY_MODULE.json').write_text(json.dumps(cfg,indent=1)+'\n')
mod=cfg['modules']
for s,r in runs:
    pf=E/(s['run']+'_emitted')/(s['run']+'_PINS.json')
    if not pf.exists():continue
    d=J(pf);mods=(s.get('covers') or {}).get('modules',[]) or ([ 'NDE_'+s['namespace'].split('NDE_')[-1] ] if s['spec_id'].startswith('NDE') else [])
    d['p1f_config']=dict(overflow_checks='ON',cargo_profile_release_overflow_checks='true',rustflags_appended='-C overflow-checks=yes',per_gate_module={m:mod.get(m,{}).get('overflow_checks','n/a (not a classified gate module)') for m in mods},
       reason='lead ruling (per gate module): all gate modules reached by this run have checked arithmetic or no arithmetic (PCQG_CONFIG_BY_MODULE.json), so ON',
       feature_set_note='Features are inferred, not recorded for the gate: audit feature set FS compiles out functions the gate contains; r0,pool-v1-kernel keeps the roots (PCQF-C3). Run features: '+str((s.get('configuration') or {}).get('features')),
       aeneas='rebuilt ORIGINAL b59d5188 sha256 959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3, verified by the controller before use')
    pf.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
rs=[dict(run=s['run'],spec=s['spec_id'],exit=r['exit_status'],wall_seconds=round(r['wall_seconds'],1),peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],cgroup_peak=r.get('cgroup_memory_peak_bytes'),source_revision=r['source_revision']) for s,r in runs]
(E/'PCQG_RECEIPT_SUMMARY.json').write_text(json.dumps(rs,indent=1)+'\n')
print(len(runs),'runs',len(fails),'failures')
