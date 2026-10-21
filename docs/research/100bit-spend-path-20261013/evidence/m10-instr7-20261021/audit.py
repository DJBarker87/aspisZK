#!/usr/bin/env python3
"""Audit the additive focused packet, not a frozen release replay."""
import hashlib, json, re, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
PACKET=HERE.parent.parent
ROOT=PACKET.parents[2]
BASE='d81c618d8f0ac6a209b36a226f681c2e894067a6'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
data=json.loads((HERE/'manifest.json').read_text())
changes=subprocess.check_output(['git','diff','--name-status',BASE],text=True).splitlines()
new=[row.split('\t')[-1] for row in changes if row.startswith('A\t') and '/lean/' in row and row.endswith('.lean')]
new+= [p for p in subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines() if '/lean/' in p and p.endswith('.lean')]
new=sorted(set(new))
errors=[]
for row in changes:
    if '/lean/' in row and row.endswith('.lean') and not row.startswith('A\t'):
        errors.append('Existing Lean source modified: '+row)
latest={a['module']:a for a in data['attempts']}
seen=set()
for a in data['attempts']:
    key=(a['module'],a['source_sha256'],a['deps_fingerprint'])
    if key in seen: errors.append('Unchanged retry: '+a['module'])
    seen.add(key)
    for k in ['argv','source_revision','source_sha256','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors']:
        if k not in a: errors.append('Missing receipt field '+k+': '+a['module'])
    if a['exit'] and not a['errors']: errors.append('Missing failure diagnostics: '+a['module'])
    if a['swaps'] != 0: errors.append('Nonzero swap: '+a['module'])
# The single final packet root must import the complete additive source set.
by_module={Path(rel).stem:ROOT/rel for rel in new}
closure=set()
def visit(module):
    if module in closure or module not in by_module: return
    closure.add(module)
    for dep in re.findall(r'^import (\S+)',by_module[module].read_text(),re.M): visit(dep)
visit('M10InstrumentationPacketM10')
if closure!=set(by_module): errors.append('Final packet root misses '+str(sorted(set(by_module)-closure)))
counts=0
pins=[]
for rel in new:
    src=ROOT/rel
    module=src.stem
    a=latest.get(module)
    if not a or a['exit']!=0:
        errors.append('No current accepted target: '+module); continue
    if a['source_sha256']!=sha(src): errors.append('Source hash stale: '+module)
    imports=a['direct_imports']
    if hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()!=a['deps_fingerprint']:
        errors.append('Fingerprint mismatch: '+module)
    for dep in imports:
        if not Path(dep['path']).is_file() or sha(dep['path'])!=dep['sha256']:
            errors.append('Stale direct import: '+module+' <- '+dep['module'])
    obj=Path(a['argv'][a['argv'].index('-o')+1])
    if not obj.is_file() or sha(obj)!=a.get('object_sha256'): errors.append('Object hash stale: '+module)
    text=src.read_text()
    code=re.sub(r'/\-[\s\S]*?\-/','',text)
    code=re.sub(r'--[^\n]*','',code)
    if re.search(r'\b(sorry|admit|axiom|native_decide|maxRecDepth|maxHeartbeats)\b',code):
        errors.append('Forbidden source token: '+module)
    names=re.findall(r'^(?:private\s+)?theorem\s+(\w+)',code,re.M)
    prints=re.findall(r'^#print axioms (\w+)',code,re.M)
    for name in names:
        if name not in prints: errors.append('Missing axiom command: '+module+'.'+name)
        if not any(re.search(r"\."+re.escape(name)+r"' ",line) for line in a['axioms']):
            errors.append('Missing accepted axiom output: '+module+'.'+name)
    for line in a['axioms']:
        if 'depends on axioms:' in line:
            match=re.search(r'axioms: \[([\s\S]*?)\]',line)
            if not match or not set(re.findall(r'[A-Za-z_.]+',match[1])).issubset({'propext','Classical.choice','Quot.sound'}):
                errors.append('Nonstandard axiom: '+line)
    counts+=len(names)
    pins.append({'module':module,'source':rel,'sha256':sha(src),'object_sha256':a.get('object_sha256'),'object_size':a.get('object_size')})
result={'status':'pass' if not errors else 'fail','scope':'focused cached-object audit; not frozen release replay',
 'completion_status':data.get('completion_status','in progress'),
 'ledger_closed':data.get('ledger_closed',False),
 'ledger_narrowed_to':data.get('ledger_narrowed_to'),
 'complete_value_and_work':data.get('complete_value_and_work',False),
 'uniform_coordinates_closed':data.get('uniform_coordinates_closed',False),
 'final_soundness_endpoint':data.get('final_soundness_endpoint',False),
 'known_obstructions':data.get('known_obstructions',[]),
 'base':BASE,'requested_base':'336305da1','baseline_mismatch_record':'audit-baseline-mismatch.json','revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 'final_packet_import_closure':len(closure),
 'new_modules':len(new),'audited_theorems':counts,'attempts':len(data['attempts']),
 'accepted_targets':sum(a['exit']==0 for a in latest.values()),
 'retained_failures':sum(a['exit']!=0 for a in data['attempts']),
 'preflight_aborts':len(data.get('preflight_aborts',[])),
 'accepted_peak_rss_bytes':max([a['peak_rss_bytes'] for a in latest.values() if a['exit']==0] or [0]),
 'all_attempt_peak_rss_bytes':max([a['peak_rss_bytes'] for a in data['attempts']] or [0]),
 'accepted_wall_seconds':sum(a['wall_seconds'] for a in latest.values() if a['exit']==0),
 'swaps':sum(a['swaps'] for a in data['attempts']),'pins':pins,'errors':errors}
(HERE/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='pins'},indent=2))
raise SystemExit(bool(errors))
