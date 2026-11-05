from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'ledger9-20261105'
# Own replay adapter: preserve validator bytes and redirect all writes.
p=E/'NHO_replay.py';s=p.read_text();start=s.index('jobs={');end=s.index('\ntry:\n path=',start)
jobs={'NGW':'slice-d-finish2-20261105/NGW_validate.py','NGY':'prepared-claim2-20261105/NGY_validate.py','NGX':'verify-observed-20261105/NGX_stage3_validate.py','NHE':'slice-d-finish3-20261106/NHE_validate.py','NHF':'candidate-prepare-20261106/NHF_validate.py','NHI':'slice-d-pair-20261106/NHI_validate.py','NHH':'q-field-rows-20261106/NHH_validate.py','NHC':'pool-leaves-20261105/NHC_validate.py'}
s=s[:start]+'jobs='+repr({a:'evidence/'+p for a,p in jobs.items()})+s[end:]
s=s.replace("sys.argv=[str(path)]+(['wide',json.loads(get(path.parent/'NGH_AUDIT.json'))['review']] if task=='NGH' else [])","sys.argv=[str(path)]+(['--final'] if task=='NGY' else [])")
# Resolve committed content-addressed source snapshots rather than silently bypassing hash checks.
s=s.replace("if q in used:","""ref=Path(str(p)+'.REFERENCE.json')
 if raw_isfile(ref):
  x=json.loads(ref.read_text());z=ref.parent/x['stored_once']
  # packed refs use evidence-directory-relative paths
  if not raw_isfile(z):z=next(parent/x['stored_once'] for parent in ref.parents if raw_isfile(parent/x['stored_once']))
  data=z.read_bytes();data=lzma.decompress(data) if x.get('encoding')=='xz' else data
  assert hashlib.sha256(data).hexdigest()==x['sha256'];return data
 if q in used:""")
s=s.replace("if raw_exists(p):return raw_open(p,mode,*a,**kw)","""if not raw_exists(p) and raw_isfile(Path(str(p)+'.REFERENCE.json')):
  data=get(p);return io.BytesIO(data) if 'b' in mode else io.StringIO(data.decode())
 if raw_exists(p):return raw_open(p,mode,*a,**kw)""")
s=s.replace("Path.exists=lambda p:raw_exists(p) or rel(p) in paths","Path.exists=lambda p:raw_exists(p) or raw_isfile(Path(str(p)+'.REFERENCE.json')) or rel(p) in paths")
s=s.replace("Path.is_file=lambda p:raw_isfile(p) or rel(p) in paths","Path.is_file=lambda p:raw_isfile(p) or raw_isfile(Path(str(p)+'.REFERENCE.json')) or rel(p) in paths")
p.write_text(s)
# Files for canonical combined import and unchanged ax2 driver adaptations.
imports=(P/'NGZ_COMBINED_IMPORT.lean').read_text().splitlines()
for a in ['NGW','NGY','NGX','NHE','NHF','NHI','NHH','NHC']:
 imports.insert(-5,'import '+a+'_COMBINED_IMPORT')
(E/'NHO_COMBINED_IMPORT.lean').write_text('\n'.join(imports)+'\n')
for name in ['ProofDriver','Driver','WALKER_SOURCE.lean.txt','WALKER_CONFORMANCE.json']:
 source=P/('NGZ_'+name+('.lean' if name in ['ProofDriver','Driver']else''))
 (E/('NHO_'+name+('.lean'if name in ['ProofDriver','Driver']else''))).write_bytes(source.read_bytes().replace(b'NGZ',b'NHO') if name in ['ProofDriver','Driver']else source.read_bytes())
# Root union: historical whole forest plus every new explicit forest print and root manifest.
x=json.loads((P/'NGZ_AUDIT_ROOTS.json').read_text());roots=set(x['roots']);provenance=[]
for a in ['NGW','NGY','NGX','NHE','NHF','NHI','NHH','NHC']:
 d=next(E.parent.glob('*/'+a+'_HANDOFF.md')).parent
 for p in [*d.glob(a+'_*IMPORT.lean'),*d.glob(a+'_AUDIT_ROOTS.json')]:
  if p.suffix=='.lean':rs=re.findall(r'^#print axioms ([\w.]+)',p.read_text(),re.M)
  else:
   m=json.loads(p.read_text());rs=m.get('roots',[])if isinstance(m,dict)else m
   if not rs and isinstance(m,dict):rs=[n for group in m.get('groups',[]) for n in group]
   if not rs and isinstance(m,dict):rs=list(m)
  roots.update(rs);provenance.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),roots=rs))
roots=sorted(roots);n=30;groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)]
(E/'NHO_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups,provenance=provenance,historical='NGZ_AUDIT_ROOTS.json'),indent=1)+'\n')
# Independent static source baselines, including Lean's implicit Init.
b={r['module']:r['imports'] for r in map(json.loads,(P/'NGZ_EXPECTED_IMPORTS.jsonl').read_text().splitlines())};changes=[]
for a in ['NGW','NGY','NGX','NHE','NHF','NHI','NHH','NHC','NHO']:
 d=E if a=='NHO' else next(E.parent.glob('*/'+a+'_HANDOFF.md')).parent
 p=d/(a+'_EXPECTED_IMPORTS.jsonl')
 if p.is_file():
  for row in map(json.loads,p.read_text().splitlines()):
   if row['module']not in b:b[row['module']]=row['imports']
 for p in d.glob(a+'_*.lean'):
  s=p.read_text();v=list(dict.fromkeys(([]if re.search(r'^prelude\b',s,re.M)else['Init'])+re.findall(r'^import ([\w.]+)',s,re.M)))
  b[p.stem]=v;changes.append(dict(module=p.stem,imports=v,path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(E/'NHO_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(b.items())))
(E/'NHO_BASELINE_PROVENANCE.json').write_text(json.dumps(changes,indent=1)+'\n')
print(len(roots),'roots')
