"""Successor inventory from ALL missing certificate names, including dependencies."""
from pathlib import Path
import json,re,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parents[1];J=lambda p:json.loads(p.read_text())
gaps=J(E/'NFY_CERTIFICATE_GAPS.json');prov=J(E/'NFY_PROVENANCE.json');loaded={r['module'] for r in map(json.loads,(E/'NFY_LOADED_scan.jsonl').read_text().splitlines())};reuse=prov['module_owner'];paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines();sources={};order=[];seen=set();missing=[]
def get(n):
 if n in sources:return sources[n]
 ps=[p for p in paths if p.endswith('/'+n+'.lean') or p.endswith('/'+n.replace('.','/')+'.lean')]
 ps=sorted(ps,key=lambda p:('/sources/' in p or '/diagnostics/' in p,not p.startswith('evidence/slice-s-compose'),len(p),p))
 if not ps:missing.append(n);return None
 p=ps[0];raw=(R/p).read_bytes() if (R/p).exists() else subprocess.check_output(['git','show','HEAD:'+p],cwd=R);r=dict(module=n,path=p,sha256=hashlib.sha256(raw).hexdigest(),line_range=[1,len(raw.decode().splitlines())],imports=re.findall(r'^import ([\w.]+)',raw.decode(),re.M));sources[n]=r;return r
roots=sorted({g['unloaded_module'] for g in gaps})
def visit(n):
 if n in seen or n in loaded or n in reuse:return
 seen.add(n);r=get(n)
 if r is None:return
 for d in r['imports']:visit(d)
 order.append(n)
for n in roots:visit(n)
families={}
for prefix in sorted({n.split('_')[0] for n in roots}):
 ns=[n for n in roots if n.startswith(prefix+'_')];families[prefix]=dict(modules=ns,declarations=sorted({g['canonical_name'] for g in gaps if g['unloaded_module'] in ns}),direct_rows=sorted({g['row'] for g in gaps if g['unloaded_module'] in ns}))
out=dict(status='UNCOMPILED_SUCCESSOR_INPUTS_ONLY',direct_modules=roots,order=order,source_pins=sources,unresolved_source_modules=sorted(set(missing)),families=families,reused_module_map=reuse,reused_namespace_map=prov['namespace_map'],native_runs_needed=0,extraction_runs_needed=0,remaining_work='Lean-only prefix retarget of the 69 auxiliary modules and their nonreused dependencies; compile bottom-up, compose with NFY/NFX/headline, rerun exact raw audit+scan, add certificate-name admission and selected-callee propagation. No credit before those gates.')
(E/'NFY_AUXILIARY_INPUTS.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(direct=len(roots),dependency_modules=len(order),missing=sorted(set(missing)),families={f:dict(modules=len(r['modules']),declarations=len(r['declarations']),direct_rows=len(r['direct_rows'])) for f,r in families.items()})))
