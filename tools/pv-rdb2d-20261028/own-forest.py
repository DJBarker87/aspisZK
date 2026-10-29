from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028';P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
j=json.loads((E/'forest-resolution.json').read_text());mapping={m:'R1Z.PV_RDB2D_'+m.split('.')[-1] for m in j['modules'] if not m.startswith('R1Z.PV_RDB2C_')};rows=[]
for m in j['order']:
 r=j['modules'][m]
 if r['authority']=='EJR':continue
 raw=subprocess.check_output(['git','show',r['blob']]);assert hashlib.sha256(raw).hexdigest()==r['sha256']
 s=raw.decode();t=re.sub(r'^import (\S+)',lambda x:'import '+mapping.get(x[1],x[1]),s,flags=re.M)
 if m in mapping:
  p=P/(mapping[m].split('.')[-1]+'.lean');p.write_text(t)
 else:p=R/r['path'];assert p.read_text()==t
 assert re.sub(r'^import .*\n','',s,flags=re.M)==re.sub(r'^import .*\n','',t,flags=re.M)
 rows.append(dict(module=mapping.get(m,m).replace('.','/'),path=str(p.relative_to(R)),original_module=m,source=r,owned_sha256=hashlib.sha256(t.encode()).hexdigest(),changes='imports only; unchanged declarations/proofs'))
(E/'forest-owned.json').write_text(json.dumps(rows,indent=2)+'\n');print(len(rows))
