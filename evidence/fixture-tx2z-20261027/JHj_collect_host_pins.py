from pathlib import Path
import json,subprocess,shlex,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fixture=json.loads((P/'JHj_AENEAS_OBJECT_PINS.json').read_text())
headline=json.loads((R/'evidence/fixture-tx2y-20261027/JHi_HEADLINE_AENEAS_OBJECT_PINS.json').read_text())
own={p.stem:dict(source_sha256=sha(p),source_path=B+'/'+p.name) for p in (R/'lean').glob('JHj_*.lean')}
code='''import json,sys,hashlib\nfrom pathlib import Path\ndef info(p):return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)\nx=json.load(sys.stdin)\nfor cohort in ['fixture','headline']:\n for row in x[cohort]:\n  p=Path(row['path']);row['actual_sha256']=hashlib.sha256(p.read_bytes()).hexdigest();row['actual_bytes']=p.stat().st_size\n  assert row['sha256']==row['actual_sha256'] and row['bytes']==row['actual_bytes'],str(p)\n  row['sidecars']=[info(q) for q in sorted(p.parent.glob(p.name+'.*')) if q.is_file()]\nfor name,row in x['own'].items():\n p=Path(row['source_path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['source_sha256'],str(p)\n row['objects']=[info(p.with_suffix('.olean'))]+[info(q) for q in sorted(p.parent.glob(p.stem+'.olean.*')) if q.is_file()]\nprint(json.dumps(x,indent=2))'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(fixture=fixture,headline=headline,own=own)),capture_output=True,text=True)
r.check_returncode();x=json.loads(r.stdout)
for key,file in [('fixture','JHj_AENEAS_OBJECT_PINS.json'),('headline','JHj_HEADLINE_AENEAS_OBJECT_PINS.json'),('own','JHj_FINAL_HOST_OBJECTS.json')]:
 (P/file).write_text(json.dumps(x[key],indent=2)+'\n')
print(len(x['fixture']),'fixture pins;',len(x['headline']),'headline pins;',len(x['own']),'own exact-source objects')
