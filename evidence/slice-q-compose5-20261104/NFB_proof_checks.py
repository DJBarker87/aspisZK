"""Recursive source/object freshness and standard-axiom evidence admission."""
from pathlib import Path
import json,re,hashlib
from NFB_dependency_check import check_imports
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ALLOWED={'propext','Classical.choice','Quot.sound'}
def accepted(module,needed=()):
 generated=obj(E/'NFB_GENERATED.json')
 src=E/(generated[module]['path'] if module in generated else module.replace('.','/')+'.lean')
 records=[obj(p) for p in E.glob('NFB_L*/receipt.json') if obj(p).get('module')==module]
 assert records,module
 r=max(records,key=lambda r:r['attempt']);a=r['attempt']
 assert r['exit_status']==0,(module,'latest source failed',a)
 rel=module.replace('.','/')+'.lean'
 assert sha(src)==r['source_hashes'][rel],(module,'source drift')
 o=obj(E/a/'object.json');assert o['source_sha256']==sha(src)
 ad=obj(E/(a+'-admission.json'));assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['command'][r['command'].index('-M7000')]=='-M7000'
 assert r['swaps']=='0'
 check_imports(src,E,generated)
 text=src.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',text)
 if module not in generated:assert not re.search(r'\b(maxHeartbeats|maxRecDepth)\b',text)
 tops=re.findall(r'^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9]*)',text,re.M)
 lines=r['print_axioms']
 assert all(any(line.split("'",2)[1].endswith('.'+name) for line in lines if "'" in line) for name in tops),(module,'missing top audit')
 for name in needed:assert any("'"+name+"'" in line for line in lines),(module,name)
 for line in lines:
  match=re.search(r'depends on axioms: \[([^\]]*)\]',line)
  if match:assert set(x.strip() for x in match[1].split(',') if x.strip())<=ALLOWED,(module,line)
  else:assert 'does not depend on any axioms' in line
 return dict(module=module,attempt=a,source_sha256=sha(src),object_sha256=o['sha256'],print_axioms=lines,source_revision=r['source_revision'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'])
if __name__=='__main__':
 import sys
 print(json.dumps(accepted(sys.argv[1]),indent=1))
