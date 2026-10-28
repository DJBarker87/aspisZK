from pathlib import Path
import json,sys,subprocess,re,hashlib
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdb2c-20261028'
label=sys.argv[1];j=json.loads((E/(label+'-resolution.json')).read_text());assert not j['missing']
mapping={m:'R1Z.PV_RDB2C_'+m.split('.')[-1] for m in j['modules']}
rows=[]
for m in j['order']:
 r=j['modules'][m];raw=subprocess.check_output(['git','show',r['blob']],cwd=R);assert hashlib.sha256(raw).hexdigest()==r['sha256']
 s=raw.decode();t=re.sub(r'^import (\S+)',lambda x:'import '+mapping.get(x[1],x[1]),s,flags=re.M)
 assert re.sub(r'^import .*\n','',s,flags=re.M)==re.sub(r'^import .*\n','',t,flags=re.M)
 p=P/(mapping[m].split('.')[-1]+'.lean')
 if p.exists():assert p.read_text()==t
 else:p.write_text(t)
 rows.append(dict(module=mapping[m].replace('.','/'),original_module=m,source=r,owned_sha256=hashlib.sha256(t.encode()).hexdigest(),changes='imports only; no declaration, proof, option, dictionary or emitted body edit'))
(E/(label+'-owned.json')).write_text(json.dumps(rows,indent=2)+'\n');print(len(rows))
