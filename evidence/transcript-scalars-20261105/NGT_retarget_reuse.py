"""Import/name-only canonical retarget of immutable sampler support.
No theorem statement or proof tactic changes. Records every original source hash.
"""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
mods={x['module']:x['imports'] for x in map(json.loads,(E.parent/'slice-d-prepared-20261105/NGN_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
paths=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines();pathset=set(paths)
canonical={n.removeprefix('RPz7_'):n for n in mods if n.startswith('RPz7_')}
cache={};provenance={};visiting=set();order=[]
def read(n):
 direct=['lean/'+n.replace('.','/')+'.lean','docs/research/100bit-spend-path-20261013/lean/'+n.replace('.','/')+'.lean']
 candidates=[p for p in direct if p in pathset]
 if not candidates:
  candidates=[p for p in paths if p.endswith('/'+n.replace('.','/')+'.lean') and '/sources/' in p]
 if not candidates:return None
 p=candidates[0];s=subprocess.check_output(['git','show','HEAD:'+p],text=True);provenance[n]=dict(path=p,sha256=hashlib.sha256(s.encode()).hexdigest());return s

def visit(n):
 if n in canonical:return canonical[n]
 if n in cache:return cache[n][0]
 if n in visiting:raise ValueError('cycle '+n)
 visiting.add(n);s=read(n)
 if s is None:visiting.remove(n);cache[n]=(n,None);return n
 imps=re.findall(r'^import ([\w.]+)',s,re.M)
 new=[visit(i) for i in imps]
 changed=new!=imps
 mapped='NGT_'+n.replace('.','_') if changed else n
 cache[n]=(mapped,s);visiting.remove(n)
 if changed:order.append(n)
 return mapped
for n in ['NBL_SamplerNative','NBL_SamplerDebug','NBL_BlockTrace','NBA_Rho','NBL_ScalarHashReplay','NBL_RhoConstruct','NBL_InitTrace']:visit(n)
renames={n:cache[n][0] for n in order}
for n in order:
 mapped,s=cache[n]
 s=re.sub(r'^import ([\w.]+)',lambda m:'import '+(canonical.get(m[1]) or cache.get(m[1],(m[1],))[0]),s,flags=re.M)
 for old,new in sorted(renames.items(),key=lambda x:-len(x[0])):
  s=re.sub(r'(?<![\w])'+re.escape(old)+r'(?![\w])',new,s)
 (E/(mapped+'.lean')).write_text(s)
(E/'NGT_RETARGET_REUSE.json').write_text(json.dumps(dict(canonical_imports=canonical,renames=renames,order=[renames[n] for n in order],provenance={n:provenance[n] for n in order}),indent=2))
print(json.dumps(dict(count=len(order),modules=[renames[n] for n in order]),indent=1))
