from pathlib import Path
import json,re,shutil
E=Path(__file__).resolve().parent
seeds=json.loads((E/'NNI_SEED_INPUTS.json').read_text());known={r['path'] for r in seeds};mods=['LIBB_ReturnObservation','LIBB_ReturnRun','LIBB_ReturnTrace','LIBB_Tx2AuthGate','LIBB_V2Star']
pins={}
for p in sorted((E.parent/'libb-20261111').glob('LIBB_L*/receipt.json')):
 x=json.loads(p.read_text())
 if x['exit_status']!=0:continue
 for z in x['deps_fingerprint']['selected_objects'].values():
  if Path(z['path']).stem in mods and '/LIBB_objects/' in z['path']:pins[z['path']]=z
for z in pins.values():
 if z['path']not in known:seeds.append(dict(tag='LIBBnew',path=z['path'],relative=Path(z['path']).name,sha256=z['sha256'],bytes=0))
(E/'NNI_LIBB_ADDITIONAL_PINS.json').write_text(json.dumps(list(pins.values()),indent=1)+'\n')
(E/'NNI_SEED_INPUTS.json').write_text(json.dumps(seeds,indent=1)+'\n')
p=E/'NNI_PATHS.json';paths=json.loads(p.read_text());paths.insert(0,'/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNI_20261111/LIBBnew_seed');p.write_text(json.dumps(paths,indent=1)+'\n')
# All manifest module namespaces with committed sources are explicit imports.
roots=json.loads((E/'NNI_AUDIT_ROOTS.json').read_text())['roots'];old=set(json.loads((E.parent/'ledger25-20261111/NMQ_AUDIT_ROOTS.json').read_text())['roots']);ns={r.removeprefix('AspisR1.').split('.')[0] for r in set(roots)-old}
text=(E/'NNI_COMBINED_IMPORT.lean').read_text();imports=re.findall(r'^import\s+([\w.]+)',text,re.M);extra=[]
for mod in sorted(ns):
 if any((E.parent/d/(mod+'.lean')).exists() for d in ['tx1-principal-20261111','tx2-auth-20261111','lib-20261111','libb-20261111','libc-20261111']) and mod not in imports:extra.append(mod)
text='\n'.join('import '+m for m in imports+extra)+'\n'+'\n'.join(l for l in text.splitlines() if not l.startswith('import '))+'\n';(E/'NNI_COMBINED_IMPORT.lean').write_text(text)
p=E/'NNI_EXPECTED_IMPORTS.jsonl';x={r['module']:r['imports']for r in map(json.loads,p.read_text().splitlines())};x['NNI_COMBINED_IMPORT']=list(dict.fromkeys(['Init']+imports+extra));p.write_text(''.join(json.dumps(dict(module=k,imports=v))+'\n'for k,v in sorted(x.items())))
for n in ['NNI_CACHE_IMPORTS.json.xz','NNI_CACHE_IMPORTS.json.sha256']:shutil.copy2(E/n,E/n.replace('IMPORTS','IMPORTS_INITIAL'))
print('extra imports',len(extra),'additional pins',len(pins))
