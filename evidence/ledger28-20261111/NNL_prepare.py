from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger27-20261111';N=E.parent/'tx1-principal-20261111'
B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNL_20261111'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):(E/('NNL_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
prior=J(P/'NNK_AUDIT_ROOTS.json');extra=set()
for name in ['NNG_F9094','NNG_R4094','NNG_R4Final']:
 x=J(N/(name+'_AUDIT_ROOTS.json'));extra.update(x.get('roots',[]));extra.update(r for g in x['groups']for r in g)
new=sorted(extra-set(prior['roots']))
# Retain all predecessor pre-split batches. New library-heavy roots get small,
# cost-balanced windows after measured scheduling, never a failed wide batch.
own=['NNL_Domains.'+n for n in ['exact094','exact328','domain094','domain328']]
groups=prior['groups']+[new[i:i+16]for i in range(0,len(new),16)]
groups[-1]+=own
library=J(E.parent/'lib-20261111/LIB_AUDIT_ROOTS.json');addition=set(library.get('roots',[]))|{r for g in library['groups']for r in g}|{'RSL.TX1_094.rejects_constErr','RSL.TX1_094.domain_needs_P1880','RSL.TX1_328.rejects_silentRet','RSL.TX1_328.ref_admits_abort'}
addition=sorted(addition-set(prior['roots'])-extra-set(own))
for i,r in enumerate(addition):groups[51+i%18].append(r)
extra.update(addition)
put('AUDIT_ROOTS',dict(roots=sorted(set(prior['roots'])|extra|set(own)),groups=groups));put('AUDIT_MODULES',[['NNL_COMBINED_IMPORT']]*len(groups))
put('NEW_ROOTS',new)
paths=[B+'/NNL_candidateR4',B+'/NNL_candidateF9',B+'/NNL_candidateRSL3',B+'/NNL_candidateOwn',B+'/NNL_libraryF9',B+'/NNL_previous']+J(P/'NNK_PATHS.json')
put('PATHS',list(dict.fromkeys(paths)))
put('SEED_CONFIG',dict(candidate_paths=J(N/'NNG_L975/receipt.json')['env']['LEAN_PATH'].split(':')[:4],library_export='/home/dombarker/project-offloads/codex-cx-lib-20261111/LIB_exports_f9_20261111',previous=J(P/'NNK_EXPORT.json'),previous_pins=J(P/'NNK_CLOSURE_PINS.json.xz')))
combined='import NNK_COMBINED_IMPORT\nimport NNG_R4094_COMBINED\nimport NNG_R4Final_COMBINED\nimport NNL_Domains\nimport NNG_F9094_COMBINED\nimport LIB_ParseShape094\nimport LIB_FullInstances\nimport LIBB_V2Star\nimport LIBC_COMBINED_IMPORT\nimport RPx_Deployed\n#print axioms AspisR1.NNG_Candidate094.candidate\n#print axioms AspisR1.NNG_Candidate328.candidate\n#print axioms AspisR1.RPx_Deployed.deployed\n'
(E/'NNL_COMBINED_IMPORT.lean').write_text(combined)
(E/'NNL_Driver.lean').write_text((P/'NNK_Driver.lean').read_text().replace('NNK_','NNL_'))
expected={json.loads(l)['module']:json.loads(l)['imports']for l in(P/'NNK_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
for folder in ['tx1-principal-20261111','lib-20261111','libb-20261111','libc-20261111','rowspec-lead-20261107','ledger28-20261111']:
 for p in(E.parent/folder).glob('*.lean'):
  expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
# Producer privately rebuilt canonical RSL modules at revision4.
for p in (N/'NNG_rev4_inputs').glob('*.lean'):
 expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
if(E/'NNL_IMPORT_REPAIR.json').exists():
 for row in J(E/'NNL_IMPORT_REPAIR.json')['pins']:
  source=__import__('subprocess').check_output(['git','show','HEAD:'+row['source']]);assert hashlib.sha256(source).hexdigest()==row['sha256']
  expected[row['module']]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',source.decode(),re.M)))
(E/'NNL_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=k,imports=v))+'\n'for k,v in sorted(expected.items())))
put('ROOT_PLAN',dict(previous_roots=len(prior['roots']),new_roots=len(new)+len(own)+len(addition),producer_new_roots=len(new),own_new_roots=len(own),library_nonvacuity_roots=len(addition),groups=len(groups),previous_groups=len(prior['groups']),group_sizes=[len(g)for g in groups]))
print(json.dumps(J(E/'NNL_ROOT_PLAN.json')))
