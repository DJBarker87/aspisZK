"""Complete Pool source closure and canonical owner-only deterministic retarget."""
from pathlib import Path
import json,re,subprocess,hashlib,sys
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
base=J(P/'slice-s-retarget-20261104/NFY_SOURCE_GRAPH.json')
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines()
paths=[p for p in paths if p.endswith('.lean') and not re.search(r'/[A-Z]+_[LB]\d+/',p)]
index={}
for p in paths:index.setdefault(Path(p).name,[]).append(p)
def source(n):
 if n in base:return base[n]
 ps=index.get(n.split('.')[-1]+'.lean',[])+index.get(n+'.lean',[])
 ps=[p for p in ps if p.endswith('/'+n.replace('.','/')+'.lean') or p.endswith('/'+n+'.lean')]
 ps=sorted(set(ps),key=lambda p:(0 if p.startswith('lean/') else 1,bool(re.search('diagnostics|/sources/|/scratch/',p)),len(p),p))
 if not ps:raise KeyError(n)
 p=ps[0];raw=subprocess.check_output(['git','show','HEAD:'+p]);t=raw.decode()
 base[n]=dict(path=p,source=t,sha256=H(raw),imports=re.findall(r'^import ([\w.]+)',t,re.M));return base[n]
reuse={};rename={}
for d,f in [('slice-q-phase-20261104','NFN_RETARGET_PROVENANCE.json'),('slice-q-accum-20261104','NFS_RETARGET_PROVENANCE.json'),('slice-s-retarget-20261104','NFY_PROVENANCE.json'),('slice-s-retarget2-20261104','NGE_PROVENANCE.json'),('slice-s-retarget3-20261104','NGF_PROVENANCE.json')]:
 x=J(P/d/f);reuse.update(x.get('module_owner',x.get('owner',{})));rename.update(x.get('namespace_map',{}))
scan={r['module']:r for r in map(json.loads,(P/'ledger8-20261105/NGJ_POOL_LOADED_scan.jsonl').read_text().splitlines())}
admitted={r['module'] for r in map(json.loads,(P/'ledger8-20261105/NGJ_LOADED_scan.jsonl').read_text().splitlines())}
starts=[]
for d,prefix in [('pool-retdata-20261104','NFO_'),('pool-retdata2-20261104','NFR_'),('pool-retdata3-20261104','NFV_')]:
 for p in sorted((P/d).glob('*.lean')):
  if p.stem in scan and not p.stem.endswith(('Driver','Coherence','WALKER','MemoryLimit','Probe')):starts.append(p.stem)
legacy=set()
def legacy_visit(n):
 if n in legacy:return
 legacy.add(n)
 for d in scan.get(n,{}).get('imports',source(n)['imports'] if n not in scan else []):legacy_visit(d)
for n in starts:legacy_visit(n)
order=[];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 if n in reuse or (n in admitted and not n.startswith(('NFO_','NFR_','NFV_'))):return
 r=source(n)
 for d in r['imports']:visit(d)
 order.append(n)
for n in starts:visit(n)
print(json.dumps(dict(starts=starts,legacy=len(legacy),copies=len(order),order=order)))
(E/'NGK_DIAGNOSIS.json').write_text(json.dumps(dict(starts=starts,legacy_closure={n:scan.get(n,{}).get('imports',[]) for n in sorted(legacy)},order=order,reused={n:reuse.get(n,n) for n in seen if n not in order}),indent=1)+'\n')
(E/'NGK_SOURCE_GRAPH.json').write_text(json.dumps({n:source(n) for n in order},indent=1)+'\n')
(E/'NGK_REUSE.json').write_text(json.dumps(dict(module_owner=reuse,namespace_map=rename),indent=1)+'\n')
owner=dict(reuse);owner.update({n:'NGK_'+n for n in order});rename.update({n:'NGK_'+n for n in order})
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
records=[]
audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
for n in order:
 r=source(n);body='\n'.join(l for l in r['source'].splitlines() if not l.startswith('import '))+'\n';after=pat.sub(lambda m:rename[m.group()],body)
 qualify = n != 'NFO_DecodeErrors' and ('open Aeneas Aeneas.Std Result AspisR1TerminalDecoder' in body or n == 'NFR_RawInverseValidator') and 'core.result.Result.map_err' in body
 if qualify:after=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1TerminalDecoder.core.result.Result.map_err',after)
 imports=list(dict.fromkeys(['Lean']+[owner.get(d,d) for d in r['imports']]))
 t=''.join('import '+d+'\n' for d in imports)+'\n'+after+audit
 p=E/(owner[n]+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t,p
 else:p.write_text(t)
 records.append(dict(source_module=n,source_path=r['path'],source_sha256=H(r['source'].encode()),source_line_range=[1,len(r['source'].splitlines())],target_module=owner[n],imports_before=r['imports'],imports_after=imports,before_body=body,after_body=after,original_body_sha256=H(body.encode()),transformed_body_sha256=H(after.encode()),changes=['imports','qualified owner/proof names only']+(['fully qualify emitted decoder map_err owner; NFY_OwnerTransport.map_err_transport'] if qualify else [])))
(E/'NGK_PROVENANCE.json').write_text(json.dumps(dict(order=order,module_owner=owner,namespace_map=rename,files=records),indent=1)+'\n')
families={}
for n in sorted(legacy):
 family='GuardBody/S2Sdk' if n.startswith(('S2Sdk','S2K_','S2G_','S2A_')) else 'Prepared/PrepQM' if 'Prepared' in n or 'PrepQM' in n else 'Phase' if 'Phase' in n else 'NED/NBN/NBK library' if n.startswith(('NED_','NBN_','NBK_')) else 'Pool proofs' if n.startswith(('NFO_','NFR_','NFV_')) else 'other'
 if n in reuse or n in order:families.setdefault(family,[]).append((n,owner.get(n,n)))
(E/'NGK_FAMILIES.md').write_text('# NGK complete Pool closure\n\n48 selected proof modules; '+str(len(legacy))+' transitive legacy modules. Complete import adjacency is in NGK_DIAGNOSIS.json. Canonical reuse stops copying at the admitted owner, never at a function-name approximation.\n\nLegacy GuardBody, PrepQM and Phase cannot coexist with canonical owners (NGJ_L027/L028/L029). No definitional equality between those competing module identities is asserted. Their existing canonical RPz7/NFN/NFS/NFY/NGE/NGF chains are reused, including the proved full-Result map_err transport where required. Pool uses no legacy owner declaration directly: its dependencies are reached through the retargeted libraries below. Each direct qualified use, including exact before/after theorem bodies, is retained in NGK_PROVENANCE.json. Pool-local carriers are consistently renamed; shared owners are never redefined. Compile and combined scan remain required.\n\n'+''.join('## '+family+'\n\n'+''.join('- `'+n+'` → `'+m+'`\n' for n,m in ns)+'\n' for family,ns in families.items()))
(E/'NGK_RETARGET.md').write_text('# NGK retarget statements\n\nAll '+str(len(records))+' Pool proof bodies retain their exact tokens except the recorded namespace substitutions. NGK_PROVENANCE.json contains full before/after statements AND proof bodies, import lists, source hashes and line ranges. No domain, hypothesis, quantifier, Result, event order or conclusion is removed or strengthened. Existing canonical library transports are reused rather than duplicated. No new owner transport is presumed proved. Each generated module dynamically prints axioms for every local top theorem.\n')
(E/'NGK_COMBINED_IMPORT.lean').write_text('import RPx_Deployed\nimport NGJ_VERIFIER_IMPORT\n'+''.join('import '+owner[n]+'\n' for n in starts)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
