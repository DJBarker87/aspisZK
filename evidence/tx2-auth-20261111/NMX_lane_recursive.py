from NMX_formal import *
pins=json.loads((E/'NMX_lane_emitted/NMX_PINS.json').read_text())
s='''from pathlib import Path
import json,hashlib,subprocess
b=Path(%r);out=b/'NMX_lane_emitted';pins=json.loads((out/'NMX_PINS.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert pins['charon_exit']==0 and sha(out/'lane.llbc')==pins['llbc_sha256']
assert sha(Path(pins['aeneas_command'][0]))==pins['tools']['aeneas-b59d5188-extended']
ds=json.loads((out/'NMX_DECLARATIONS.json').read_text())
match=[f for f in ds if [x['Ident'][0] for x in f['name'] if 'Ident' in x]==['aspis_statement','atomic_statement','decode_digest_canonical']]
assert len(match)==1 and match[0]['body_kind']=='Opaque'
pins['validated_digest_owner']=match[0]
pins['continuation']='NMX_L667: explicit recursive loop encoding; same frozen LLBC, no Charon rerun'
pins['aeneas_command']=pins['aeneas_command'][:-1]+['-loops-to-rec']+pins['aeneas_command'][-1:]
r=subprocess.run(pins['aeneas_command'],cwd=b)
pins['aeneas_exit']=r.returncode;pins['exit']=r.returncode
pins['outputs']={str(p.relative_to(out)):sha(p) for p in (out/'raw').rglob('*') if p.is_file()}
(out/'NMX_PINS.json').write_text(json.dumps(pins,indent=2)+'\\n')
assert sha(b/'NMX_src/Cargo.lock')==pins['lock_before']==pins['lock_after']
raise SystemExit(r.returncode)
''' % B
env=json.loads((E/'NMX_R3_ENV.json').read_text())
r=run('NMX_L667','inspect','NMX_lane_continuation',['python3','NMX_lane_recursive_host.py'],{'NMX_lane_recursive_host.py':s},env_extra=env)
# Read-only artifact retention after this unique Aeneas continuation.
z=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r})/'NMX_lane_emitted'
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in b.rglob('*') if p.is_file() and p.suffix not in ['.olean','.ir']}}))
''');assert z.returncode==0,z.stderr
import base64
for n,t in json.loads(z.stdout).items():
 raw=base64.b64decode(t);p=E/'NMX_lane_emitted'/n;p.parent.mkdir(parents=True,exist_ok=True)
 if len(raw)>20_000_000:
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
sys.exit(r['exit_status'])
