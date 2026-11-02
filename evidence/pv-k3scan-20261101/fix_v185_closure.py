from pathlib import Path
import subprocess,json,hashlib,lzma,base64
E=Path(__file__).resolve().parent;REF='ea4eca5b147920a19ccde05e2cc95c4d2bad25c8';REV='bd47052f039ae2d96060acb5607fe652ebe193d4';files={};records=[]
for snap in ['candidate-c3-snapshot.json','candidate-include-snapshot.json']:
 s=json.loads(subprocess.check_output(['git','show',REF+':evidence/pv-cblib-20261027/'+snap]))
 for n,m in s['files'].items():
  h=m['sha256'] if isinstance(m,dict) else m;b=subprocess.check_output(['git','show',REV+':'+n]);assert hashlib.sha256(b).hexdigest()==h,n
  files[n]=base64.b64encode(b).decode();records.append({'path':n,'sha256':h,'source':REV+':'+n,'snapshot':snap})
raw=json.dumps(files).encode();(E/'V185-closure-addendum.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'V185-closure-addendum.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'V185-PREFLIGHT-REPAIR.json').write_text(json.dumps({'id':'K79206','failure':'cargo metadata exit101 before scope/compiler: missing c3/build/Cargo.toml','charged_Kani':0,'STARTED_exists':False,'correction':'Recover candidate-c3 and candidate-include hash-pinned snapshot additions; no harness change','same_unlaunched_ID_reused':True,'prior_metadata_retained':'host/K79206-preflight','files':records},indent=2)+'\n')
print(len(files),'hash-checked omitted dependency/include files recovered')
