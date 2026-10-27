import json,pathlib,subprocess
p=pathlib.Path(__file__).parent
x=json.loads((p/'audit.json').read_text())
script='''import json,pathlib,hashlib
b=pathlib.Path('/home/dombarker/project-offloads')
e=json.loads((b/'r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[b/'aspis-joint-20261019/objects']+[pathlib.Path(s) for s in e['LEAN_PATH'].split(':')]
r={}
for m in MODS:
 found=[p/(m+'.olean') for p in paths if (p/(m+'.olean')).is_file()]
 r[m]=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in dict.fromkeys(found)]
print(json.dumps(r))
'''.replace('MODS',repr(list(x['modules'])))
r=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script.encode()))
(p/'effective_objects.json').write_text(json.dumps(r,indent=2)+'\n')
print('Effective object overrides:',[(m,v[0]['path']) for m,v in r.items() if v and '/aspis-joint-20261019/objects/' not in v[0]['path']])
print('Conflicting object variants:',[(m,len(set(z['sha256'] for z in v))) for m,v in r.items() if len(set(z['sha256'] for z in v))>1])
