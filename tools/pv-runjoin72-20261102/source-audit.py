"""Check current accepted sources and recorded axiom output; no compiler invocation."""
from pathlib import Path
import json,re,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin72-20261102'
rec=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())];checks=[]
for v in rec:
 if not v['accepted']:continue
 p=Path(v['source']['path']);b=subprocess.check_output(['git','show','HEAD:'+str(p)],cwd=R)
 assert hashlib.sha256(b).hexdigest()==v['source_sha256'],v['module']
 s=(R/p).read_text()
 hits=[x for x in ['sorry','native_decide','axiom','set_option maxHeartbeats','set_option maxRecDepth'] if re.search(r'\b'+re.escape(x)+r'\b',s)]
 assert not hits,(str(p),hits)
 for a in v['axioms']:
  if 'depends on axioms:' in a:
   axs=re.search(r'\[([^]]*)\]',a).group(1)
   assert set(x.strip() for x in axs.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},(v['module'],a)
 checks.append(dict(module=v['module'],sha256=v['source_sha256'],source_revision=v['source_revision'],standard_axioms_only=True,source_hash_match=True))
(E/'accepted-source-audit.json').write_text(json.dumps(checks,indent=2)+'\n')
print('Accepted source/axiom checks:',len(checks))
