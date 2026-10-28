from pathlib import Path
import json,re
E=Path('evidence/pv-batch2-20261027/batch2d');L=Path('docs/research/v8-r0-zk-20261009/lean');h5=json.loads((E/'H5-SOURCE-PINS.json').read_text());seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 p=Path(h5[m]['path']) if m in h5 else L/(m+'.lean')
 for dep in re.findall(r'^import (\S+)',p.read_text(),re.M):
  dep=dep.replace('.','/')
  if dep.startswith('R1Z/PV_B2_') or dep in h5:visit(dep)
 order.append(m)
visit('R1Z/PV_B2_C_NativeGammaCarrier')
t=json.loads((E/'TALLY.json').read_text());done={a['module'] for a in t['attempts'] if a.get('exit')==0};order=[m for m in order if m not in done]
(E/'SAMPLER-DEPENDENT-QUEUE.json').write_text(json.dumps(order,indent=2)+'\n');print(len(order));print('\n'.join(order))
