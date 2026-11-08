from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger28-20261111';N=E.parent/'tx1-principal-20261111';X=E.parent/'tx2-auth-20261111'
B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):(E/('NNM_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
prior=J(P/'NNL_AUDIT_ROOTS.json');extra={r for g in J(N/'NNG_Resume_AUDIT_ROOTS.json')['groups'] for r in g}
for n in ['NMX_R4','NMX_R6','NMX_R9']:
 f=X/(n+'_AUDIT_ROOTS.json');x=J(f);extra.update(x.get('roots',[]));extra.update(r for g in x['groups']for r in g)
own=['NNM_Domains.'+n for n in ['exact345','exact344','exact233','exact242','exact241','domain345','domain344','domain233','domain242']]
new=sorted(extra-set(prior['roots']));groups=prior['groups']+[new[i:i+14]for i in range(0,len(new),14)]+[own]
put('AUDIT_ROOTS',dict(roots=sorted(set(prior['roots'])|extra|set(own)),groups=groups));put('AUDIT_MODULES',[['NNM_COMBINED_IMPORT']]*len(groups));put('NEW_ROOTS',new)
paths=[B+'/NNM_tx1',B+'/NNM_wrapperR4',B+'/NNM_tx2',B+'/NNM_previous']+J(P/'NNL_PATHS.json');put('PATHS',list(dict.fromkeys(paths)))
put('SEED_CONFIG',dict(previous_export=J(P/'NNL_EXPORT.json'),previous_pins=J(P/'NNL_CLOSURE_PINS.json.xz'),tx1_paths=J(N/'NNG_L1111/receipt.json')['env']['LEAN_PATH'].split(':')[:6],tx2=J(X/'NMX_R9_CLOSURE_PINS.json.xz'),tx2_export=J(X/'NMX_R9_EXPORT.json')))
combined='import NNL_COMBINED_IMPORT\nimport NNG_ActualCandidate345\nimport NNG_Candidate344\nimport NMX_R4_Authentication\nimport NMX_R6_SourceExact242\nimport NMX_R9_StageTwo\nimport NNM_Domains\nimport LIB_FullInstances\nimport LIBB_V2Star\nimport LIBC_COMBINED_IMPORT\nimport RPx_Deployed\n'
# All new supplier roots must be loaded, including support declarations not on a candidate's transitive path.
for r in new:
 # Source module ownership is reconstructed from current print manifests below.
 pass
mods=set()
for r in new:
 ns=r.removeprefix('AspisR1.').split('.')[0]
 if ns.startswith(('NNG_','NMX_')):mods.add(ns)
combined+=''.join('import '+m+'\n'for m in sorted(mods))
(E/'NNM_COMBINED_IMPORT.lean').write_text(combined)
for n in ['Driver.lean','batch.py']:(E/('NNM_'+n)).write_text((P/('NNL_'+n)).read_text().replace('NNL_','NNM_'))
expected={json.loads(l)['module']:json.loads(l)['imports']for l in(P/'NNL_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
for folder in [N,X,E]:
 for p in folder.rglob('*.lean'):
  if '/sources/'in str(p):continue
  expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
(E/'NNM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=k,imports=v))+'\n'for k,v in sorted(expected.items())))
put('ROOT_PLAN',dict(previous_roots=len(prior['roots']),new_roots=len(new)+len(own),groups=len(groups),previous_groups=len(prior['groups']),group_sizes=[len(g)for g in groups]))
print(J(E/'NNM_ROOT_PLAN.json'))
