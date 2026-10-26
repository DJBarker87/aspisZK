"""Proof-source import adaptation only; no launcher/build/monitor changes."""
from pathlib import Path
import subprocess,re,json,hashlib
R=Path(__file__).resolve().parents[2];P=R/'evidence/finish-install2-20261026'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines()
index={}
for s in paths:
 if s.endswith('.lean') and ('/sources/' in s or '/lean/' in s or s.startswith('lean/') or '/upstream/' in s):
  index.setdefault(Path(s).stem,[]).append(s)
def score(s):
 return (int('/history/' in s or '/failed' in s or '/superseded' in s),int('/sources/' not in s),int('20261024' not in s),len(s))
def choose(n):
 ps=index.get(n,[])
 return min(ps,key=score) if ps else None
special={'AspisR1S9ProductionPairCutV1.Funs':'FIo_NativeFuns','AspisR1S9ProductionPairCutV1.Types':'FIo_NativeTypes','AspisR1S9ProductionPairCutV1.FunsExternal':'FIo_NativeExternal','AspisR1CanonicalQRaw.Funs':'FIo_QRawFuns','AspisR1CanonicalQRaw.Types':'FIo_QRawTypes'}
roots=['S9Tx2FoldedPartsV1','S9SevenFoldAssemblyV1'];sources={};order=[];visiting=set();missing=[]
def visit(n):
 if n in sources or n in special:return
 if not(n.startswith('S9') or n.startswith('AspisR1S9')):return
 path=choose(n)
 if path is None:missing.append(n);return
 if n in visiting:raise Exception('cycle '+n)
 visiting.add(n);s=(R/path).read_text();imps=re.findall(r'^import ([\w.]+)',s,re.M)
 for d in imps:visit(d)
 visiting.remove(n);sources[n]={'path':path,'sha256':hashlib.sha256(s.encode()).hexdigest(),'imports':imps};order.append(n)
for n in roots:visit(n)
ren={n:'FIo_P_'+n for n in sources};ren.update(special)
for n,v in sources.items():
 s=(R/v['path']).read_text()
 for a,b in ren.items():s=re.sub(r'(?m)^import '+re.escape(a)+r'$', 'import '+b,s)
 s=s.replace('AspisR1S9ProductionPairCutV1','FIo_Native').replace('AspisR1S9AllocationInterfaceV1.Allocation','FIo_Native.Allocation')
 s=re.sub(r'(?m)^set_option max(?:Heartbeats|RecDepth) .*\n','',s)
 p=R/'lean'/(ren[n]+'.lean');p.write_text(s);v['adapted_path']=str(p.relative_to(R));v['adapted_sha256']=hashlib.sha256(s.encode()).hexdigest()
(P/'FIo_S9-port-plan.json').write_text(json.dumps({'roots':roots,'order':order,'sources':sources,'missing':sorted(set(missing)),'adaptation':'imports only; native Pair namespace/typeclass mapped to FIo concrete body; inherited proof heartbeat/depth options removed'},indent=2)+'\n')
print(json.dumps({'modules':len(order),'missing':sorted(set(missing)),'first':order[:12]}))
