from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
js=sorted([json.loads(p.read_text())for p in E.glob('J*/receipt.json')],key=lambda d:d['attempt']);ks=[json.loads(p.read_text())for p in sorted(E.glob('K*/receipt.json'))]
assert len(js)==100 and len(ks)==6
assert len({d['attempt']for d in js})==100
allowed={'propext','Classical.choice','Quot.sound'}
manifest=json.loads((E/'AUDIT-MANIFEST.json').read_text())
for row in manifest['modules']:
 p=R/row['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
 s=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s)
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s)
for a in [43897,43898,43899]:
 d=next(d for d in js if d['attempt']==a);assert d['exit']==0
 for line in d['axioms']:
  if 'depends on axioms:' in line:
   vals={s.strip()for s in line.split('[',1)[1].rstrip(']').split(',')if s.strip()};assert vals<=allowed,line
latest=next(d for d in js if d['attempt']==43899)
assert len(latest['axioms'])==manifest['theorems'],(len(latest['axioms']),manifest['theorems'])
summary=dict(lean_charged=len(js),lean_pass=sum(d['exit']==0 for d in js),lean_failed=sum(d['exit']!=0 for d in js),kani_charged=len(ks),kani_pass=sum(d['exit']==0 for d in ks),private_refusals=[43644,43652],source_modules=manifest['source_modules'],audit_modules=3,final_theorems=manifest['theorems'],all_final_axioms_standard=True,peak_rss_kib=max(int(d['peak_rss_kib'])for d in js),swaps=sum(int(d['swaps'])for d in js),final_audit=latest,endpoint_premises_removed=0,endpoint_premises_added=0,trust_items_added=0,V380='OPEN',target_established=False)
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
s='| Attempt | Target | Exit | Wall | Peak RSS KiB | Swap | Revision |\n|---|---|---:|---|---:|---:|---|\n'
for d in js:
 s+=f"| [J{d['attempt']}](J{d['attempt']}/receipt.json) | {d['module']} | {d['exit']} | {d['wall']} | {d['peak_rss_kib']} | {d['swaps']} | {d['source_revision'][:10]} |\n"
for i,d in enumerate(ks,1):
 s+=f"| [K{i:02}](K{i:02}/receipt.json) | {d['target']} | {d['exit']} | {d['wall']} | {d['peak_rss_kib']} | {d['swaps']} | {d['source_revision'][:10]} |\n"
(E/'INDEX.md').write_text(s)
(E/'AXIOMS.md').write_text('# Final focused audit\n\n'+str(manifest['theorems'])+' declarations; all axiom sets are subsets of propext, Classical.choice, Quot.sound. Failed elaboration outputs are excluded.\n\n```text\n'+'\n'.join(latest['axioms'])+'\n```\n')
print(json.dumps({k:v for k,v in summary.items()if k!='final_audit'},indent=2))
