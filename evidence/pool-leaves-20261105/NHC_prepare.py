from pathlib import Path
import json,re,hashlib,sys
E=Path(__file__).resolve().parent;P=E.parent;G=P/'pool-prefix-20261105';K=P/'pool-retarget-20261105'
H=lambda b:hashlib.sha256(b).hexdigest()
k=json.loads((K/'NGK_PROVENANCE.json').read_text());owner=k['module_owner'];names=dict(k['namespace_map'])
# Exact recursive source closure of the successfully audited NGG packet, excluding drivers.
roots=re.findall(r'^import (NGG_[\w.]+)',(G/'NGG_COMBINED_IMPORT.lean').read_text(),re.M)
order=[];seen=set();src={}
def visit(n):
 if n in seen:return
 seen.add(n)
 if not n.startswith('NGG_'):return
 p=G/(n.replace('.','/')+'.lean');t=p.read_text();src[n]=(p,t)
 for d in re.findall(r'^import ([\w.]+)',t,re.M):visit(d)
 order.append(n)
for n in roots:visit(n)
assert len(order)==27,(len(order),order)
# Prefix source module and emitted namespace families, consistently including local carriers.
for n in order:
 owner[n]='NHC_'+n
 names[n]='NHC_'+n
for n in ['NGG_Ref','NGG_SpineRef']:names[n]='NHC_'+n
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(names,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
records=[]
audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
for n in order:
 p,t=src[n];body='\n'.join(l for l in t.splitlines() if not l.startswith('import '))+'\n'
 imports=re.findall(r'^import ([\w.]+)',t,re.M);after=pat.sub(lambda m:names[m.group()],body)
 newimports=list(dict.fromkeys(['Lean']+[owner.get(d,d) for d in imports]))
 out=''.join('import '+d+'\n' for d in newimports)+'\n'+after+audit
 dest=E/(owner[n].replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True)
 if '--check' in sys.argv:assert dest.read_text()==out,dest
 else:dest.write_text(out)
 records.append(dict(source_module=n,source_path=str(p.relative_to(E.parents[1])),source_sha256=H(t.encode()),source_line_range=[1,len(t.splitlines())],target_module=owner[n],imports_before=imports,imports_after=newimports,before_body=body,after_body=after,target_sha256=H(out.encode())))
prov=dict(order=order,module_owner=owner,namespace_map=names,files=records,canonical_provenance_sha256=H((K/'NGK_PROVENANCE.json').read_bytes()),changes=['imports','qualified owner names','all-local-theorem axiom printing'])
(E/'NHC_PROVENANCE.json').write_text(json.dumps(prov,indent=1)+'\n')
(E/'NHC_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\n'+''.join('import '+owner[n]+'\n' for n in roots)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
(E/'NHC_RETARGET.md').write_text('# NHC deterministic retarget\n\n27 NGG modules, including both emitted reference families, are copied under NHC_. Existing NGK/NFY canonical owners are imported, never redefined. Full before/after proof bodies, imports, line ranges and source hashes are in NHC_PROVENANCE.json. No quantifier, domain, Result or conclusion changes. No production row closes by retarget. Focused compilation and combined headline audit are pending.\n')
print(json.dumps(dict(modules=len(order),order=order)))
