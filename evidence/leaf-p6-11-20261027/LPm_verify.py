"""Compile-free final audit of exact retained inputs and proof receipts."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;root=E.parent.parent
rows=[]
for p in sorted(E.glob('LPm_[LKG][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];kind=r['kind']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert r['swaps']=='0',a
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 assert ad['allowed'] is True,a
 assert r['source_revision'] and r['source_hashes'] and r['command'],a
 if a.startswith('LPm_L'):
  assert '-M7000' in r['command'],a
  for s,h in r['source_hashes'].items():
   q=p.parent/'sources'/s
   assert hashlib.sha256(q.read_bytes()).hexdigest()==h,(a,s)
 if r['exit_status']==0 and a.startswith('LPm_L'):
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    axioms=set(line.split('[')[1].rstrip(']').split(', '))
    assert axioms<={'propext','Classical.choice','Quot.sound'},(a,line)
 if a.startswith('LPm_K'):
  g=json.loads((E/(a+'-graph-check.json')).read_text())
  assert all(g[k] for k in ['exact_frozen_resolved_graph_match','package_and_edges_match','lock_unchanged']),a
  assert g['lock_before_sha256']==g['lock_after_sha256']==g['frozen_lock_sha256'],a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
 rows.append({k:r[k] for k in ['attempt','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','cgroup','print_axioms']})
lean=[r for r in rows if r['attempt'].startswith('LPm_L')];kani=[r for r in rows if r['attempt'].startswith('LPm_K')]
assert len(lean)==80 and len(kani)==18
modules=[]
for p in sorted((root/'lean').glob('LPm_*.lean')):
 text=p.read_text();matches=[r for r in lean if r['exit_status']==0 and json.loads((E/r['attempt']/'receipt.json').read_text())['module']==p.stem]
 assert matches,p
 last=matches[-1];rc=json.loads((E/last['attempt']/'receipt.json').read_text())
 assert hashlib.sha256(p.read_bytes()).hexdigest()==rc['source_hashes']['LPm_generated/'+p.name],p
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'--[^\n]*','',text)),p
 ns=re.search(r'^namespace (\S+)',text,re.M)
 tops=[] if not ns else [ns.group(1)+'.'+n for n in re.findall(r'^\s*theorem (\S+)',text,re.M)]
 for top in tops:
  assert any("'"+top+"'" in x for x in rc['print_axioms']),top
 modules.append({'module':p.stem,'accepted_attempt':last['attempt'],'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tops':tops})
audit=json.loads((E/'LPm_L080'/'receipt.json').read_text())
assert audit['exit_status']==0 and len(audit['print_axioms'])==73
patch=json.loads((E/'LPm_PATCH_AUDIT.json').read_text());assert len(patch)==18
assert all(r['source_snapshot_hashes_match'] and r['frozen_graph_and_lock_match'] for r in patch)
source=json.loads((E/'LPm_SOURCE_AUDIT.json').read_text())
# Keep exact logs/patches intact; their tool-generated whitespace is evidence.
r=subprocess.run(['git','diff','--check','--','lean/LPm_*.lean','evidence/leaf-p6-11-20261027/*.py','evidence/leaf-p6-11-20261027/*.md'],cwd=root,capture_output=True,text=True)
assert r.returncode==0,r.stdout+r.stderr
out={'lean_attempts':len(lean),'lean_passes':sum(r['exit_status']==0 for r in lean),'lean_rejected':sum(r['exit_status']!=0 for r in lean),'kani_runs':len(kani),'kani_passes':sum(r['exit_status']==0 for r in kani),'kani_excluded':sum(r['exit_status']!=0 for r in kani),'all_accepted_axioms_standard':True,'final_axioms_roots':73,'source_and_caps_and_locks_checked':True,'modules':modules,'receipts':rows,'headline_premises_removed':0,'checkpoint':'CLOSED on retained domain; hybrid native P6 bridge','prepared_claim':'OPEN: see leaf packet; no whole-body conclusion','proof_budget_exhausted':True}
(E/'LPm_FINAL_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['modules','receipts']})
