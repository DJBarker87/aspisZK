from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028')
out=H/'NCR_B003'
for p in sorted((out/'diagnostics').iterdir()):
 if p.is_file() and p.stat().st_size<200000 and ('command' in p.name):
  try:j=json.loads(p.read_text())
  except ValueError:continue
  print(json.dumps({'diagnostic_file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'content':j}))
print(json.dumps({'retained_artifacts':[{'name':p.name,'bytes':p.stat().st_size} for p in (out/'artifacts').iterdir()],'note':'No key content read, no key cleanup. Artifact and diagnostics retained.'}))
t=H/'NCR_target';assert t.parent==H and t.name=='NCR_target' and not t.is_symlink()
if t.exists():shutil.rmtree(t)
print(json.dumps({'removed_only':str(t),'target_absent':not t.exists()}))
