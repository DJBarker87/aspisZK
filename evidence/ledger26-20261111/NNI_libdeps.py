from pathlib import Path
import re,json
E=Path(__file__).resolve().parent;D=E.parent/'libb-20261111';todo=['LIBB_ReturnObservation','LIBB_ReturnRun','LIBB_ReturnTrace','LIBB_Tx2AuthGate','LIBB_V2Star'];mods=set()
while todo:
 m=todo.pop()
 if m in mods:continue
 mods.add(m);p=D/(m+'.lean')
 if p.exists():todo += [n for n in re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M) if n.startswith('LIBB_')]
pins={}
for p in sorted(D.glob('LIBB_L*/receipt.json')):
 x=json.loads(p.read_text())
 if x['exit_status']==0:
  for z in x['deps_fingerprint']['selected_objects'].values():
   if Path(z['path']).stem in mods and '/LIBB_objects/' in z['path']:pins[z['path']]=z
seeds=json.loads((E/'NNI_SEED_INPUTS.json').read_text());known={r['path']for r in seeds}
for z in pins.values():
 if z['path'] not in known:seeds.append(dict(tag='LIBBnew',path=z['path'],relative=Path(z['path']).name,sha256=z['sha256'],bytes=0))
(E/'NNI_LIBB_ADDITIONAL_PINS.json').write_text(json.dumps(dict(modules=sorted(mods),pins=list(pins.values())),indent=1)+'\n');(E/'NNI_SEED_INPUTS.json').write_text(json.dumps(seeds,indent=1)+'\n')
print('dependency modules',len(mods),'pins',len(pins))
