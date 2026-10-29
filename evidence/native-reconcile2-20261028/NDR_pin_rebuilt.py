"""Read-only source/object inventory after receipt verification; no host writes/builds."""
from pathlib import Path
import hashlib, json, subprocess, time
E = Path(__file__).resolve().parent
R = E.parents[1]
B = '/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028'
verification = json.loads((E / 'NDR_VERIFICATION.json').read_text())
pins = json.loads((E / 'NDR_SOURCE_PINS.json').read_text())
missing = set(verification['missing_modules'])
rows = [r for r in pins if r['module'] not in missing]
for m in ['NDO_InstalledIdentity', 'NDO_PhaseIdentity', 'NDR_HeadlineNatives', 'NDR_PdaAxiomAudit']:
    rows.append({'module': m, 'sha256': hashlib.sha256((R / 'lean' / (m + '.lean')).read_bytes()).hexdigest()})
code = '''from pathlib import Path
import json,hashlib
base=Path(BASE)
rows=json.loads(ROWS)
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while True:
   chunk=f.read(1048576)
   if not chunk:break
   h.update(chunk)
 return h.hexdigest()
result=[]
for row in rows:
 m=row['module'];source=base/(m+'.lean');obj=base/'objects'/(m+'.olean')
 actual=sha(source)
 assert actual==row['sha256'],(m,'host source mismatch')
 result.append(dict(module=m,source_sha256=actual,object_sha256=sha(obj),object_path=str(obj),object_bytes=obj.stat().st_size))
print(json.dumps(result))
'''.replace('BASE', repr(B)).replace('ROWS', repr(json.dumps(rows)))
started = time.monotonic()
for retry in range(11):
    process = subprocess.run(['ssh', '-o', 'ControlMaster=no', '-o', 'ConnectTimeout=15',
                              'dombarker@100.108.41.90', 'python3 -'], input=code,
                             capture_output=True, text=True)
    if process.returncode != 255:
        break
    with (E / 'NDR_ATTEMPTS.jsonl').open('a') as f:
        f.write(json.dumps(dict(kind='transport', attempt='NDR_PIN', retry=retry,
                               submitted=False, exit_status=255, stderr=process.stderr)) + '\n')
    if retry < 10:
        time.sleep(60)
assert process.returncode == 0, process.stderr
result = json.loads(process.stdout)
assert len(result) == len(rows)
(E / 'NDR_REBUILT_OBJECT_PINS.json').write_text(json.dumps(dict(
    method='Streaming SHA256 of task-cache source and object files, after successful compile receipt verification; existing seed objects retain their predecessor pins. No compiler replay or host mutation.',
    wall_seconds=time.monotonic()-started, source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip(),
    standalone_plan_modules=verification['passing_modules'], extra_identity_audit_modules=4,
    entries=result), indent=2) + '\n')
print(json.dumps(dict(pinned=len(result), standalone_plan_modules=verification['passing_modules'], wall_seconds=time.monotonic()-started)))
