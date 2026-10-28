from NCG_host import *
import difflib
for config in sorted(E.glob('NCG_[KL][0-9][0-9][0-9].json')):
 a=config.stem
 if not (E/a/'receipt.json').exists():continue
 # Read-only receipt recovery, never launches or rebuilds anything.
 r=py(f'''from pathlib import Path
import json
p=Path({B!r})/{a!r}/'sources'
print(json.dumps({{str(f.relative_to(p)):f.read_text() for f in p.rglob('*') if f.is_file() and (f.suffix=='.lean' or f.name in ['NCG_native.rs','NCG_tail.rs','NCG_field_arbitrary.rs','field.rs','fast_pairing.rs'])}}))
''');assert r.returncode==0,r.stderr
 for name,s in json.loads(r.stdout).items():
  if name.endswith('.lean'):
   out=E/a/(Path(name).name+'.txt');out.write_text(s);continue
  if Path(name).name in ['field.rs','fast_pairing.rs']:
   rel=name.split('NCG_src/',1)[1]
   before=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+rel],text=True)
  else:rel=name.split('NCG_src/',1)[1];before=''
  patch=''.join(difflib.unified_diff(before.splitlines(True),s.splitlines(True),fromfile='a/'+rel if before else '/dev/null',tofile='b/'+rel))
  (E/a/(Path(name).name+'.patch')).write_text(patch)
