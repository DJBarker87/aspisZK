from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'ledger10-20261106';H=lambda b:hashlib.sha256(b).hexdigest()
prefixes=['NHK','NHN','NHG','NHS','NHM','NHJ','NHX','NHU','NHP','NHZ','NIB','NHW','NIF','NHT','NHV','NHL','NIA','NIC']
dirs={a:next(E.parent.glob('*/'+a+'_HANDOFF.md')).parent for a in prefixes}
imports=re.findall(r'^import ([\w.]+)',(P/'NHO_COMBINED_IMPORT.lean').read_text(),re.M)
for a in prefixes:
 if (dirs[a]/(a+'_COMBINED_IMPORT.lean')).exists():imports.append(a+'_COMBINED_IMPORT')
plan=['AspisR1.RPx_Deployed.deployed','AspisR1.NGR_HISTORY.saved_to_loaded','AspisR1.NGS_CARRIERS.same_inputs_or_collision','AspisR1.NGP_OracleTransport.prefix_of_native','AspisR1.NGP_OracleTransport.exact_of_returns','AspisR1.NGP_TRANSCRIPT.actual_queries','AspisR1.NHZ_DRIVER.events_from_cuts','AspisR1.NHZ_EXPERIMENT.same_law','NIB_ReadToSettlement.read_to_settlement']
# Exact writer name is read from its compiled combined manifest.
plan+=['AspisR1.NHW_WriterFromNative.under_retained_extraction']
plan+=re.findall(r'^#print axioms ([\w.]*NHW[\w.]*writer[\w.]*)',(dirs['NHW']/'NHW_COMBINED_IMPORT.lean').read_text(),re.M)
(E/'NII_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n'for m in dict.fromkeys(imports))+''.join('#print axioms '+n+'\n'for n in plan))
(E/'NII_PLAN_STATEMENTS.lean').write_text('import NII_COMBINED_IMPORT\nset_option pp.fullNames true\nset_option pp.universes true\nset_option pp.explicit true\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n'for n in plan))
roots=set(json.loads((P/'NHO_AUDIT_ROOTS.json').read_text())['roots']);provenance=[]
def names(x):
 if isinstance(x,dict):
  if isinstance(x.get('root'),str):yield x['root']
  for v in x.values():yield from names(v)
 elif isinstance(x,list):
  for v in x:yield from names(v)
for a,d in dirs.items():
 ps=[*d.glob(a+'_*IMPORT.lean'),*d.glob(a+'_AUDIT_ROOTS.json'),*d.glob(a+'_AUDIT.json')]
 for p in ps:
  if p.suffix=='.lean':ns=re.findall(r'^#print axioms ([\w.]+)',p.read_text(),re.M)
  else:
   x=json.loads(p.read_text());ns=list(names(x))
   if p.name.endswith('_ROOTS.json'):
    v=x.get('roots',[])if isinstance(x,dict)else x
    ns+=v if isinstance(v,list)else []
    if isinstance(x,dict):ns += [n for g in x.get('groups',[])for n in g]
  ns=[n for n in ns if isinstance(n,str)and not n.startswith(('NEP_Planted.','NEP_Mutate'))]
  roots.update(ns);provenance.append(dict(path=str(p.relative_to(R)),sha256=H(p.read_bytes()),roots=ns))
roots.update(plan);roots=sorted(roots);n=29
(E/'NII_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)],provenance=provenance,historical='NHO_AUDIT_ROOTS.json'),indent=1)+'\n')
b={r['module']:r['imports']for r in map(json.loads,(P/'NHO_EXPECTED_IMPORTS.jsonl').read_text().splitlines())};differences=[]
for a,d in dirs.items():
 p=d/(a+'_EXPECTED_IMPORTS.jsonl')
 if p.exists():
  for row in map(json.loads,p.read_text().splitlines()):
   m=row['module'];v=row['imports']
   if m in b and b[m]!=v:differences.append(dict(module=m,existing=b[m],candidate=v,source=str(p.relative_to(R))))
   else:b[m]=v
 for p in d.glob(a+'_*.lean'):
  s=p.read_text();v=list(dict.fromkeys(([]if re.search(r'^prelude\b',s,re.M)else['Init'])+re.findall(r'^import ([\w.]+)',s,re.M)))
  # Current module sources are definitive independent static manifest inputs.
  if p.stem in b and b[p.stem]!=v:differences.append(dict(module=p.stem,existing=b[p.stem],candidate=v,source=str(p.relative_to(R))))
  b[p.stem]=v
for p in E.glob('NII_*.lean'):
 b[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NII_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(b.items())))
(E/'NII_BASELINE_DIFFERENCES.json').write_text(json.dumps(differences,indent=1)+'\n')
for n in ['ProofDriver','Driver']:
 old=(P/('NHO_'+n+'.lean')).read_text();new=(E/('NII_'+n+'.lean')).read_text();(E/('NII_'+n+'.diff')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='NHO_'+n+'.lean',tofile='NII_'+n+'.lean')))
for n in ['WALKER_SOURCE.lean.txt','WALKER_CONFORMANCE.json']:(E/('NII_'+n)).write_bytes((P/('NHO_'+n)).read_bytes())
print(json.dumps(dict(roots=len(roots),forests=len(imports),baseline_differences=len(differences),plans=plan)))
