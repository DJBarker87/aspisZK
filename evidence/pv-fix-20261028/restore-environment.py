from pathlib import Path
import json
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');pre=json.loads((D/'preflight.json').read_text())
for cohort in ['rdcd','rdeac']:
 env=pre[cohort]['original_environment'];(D/(cohort+'-env.json')).write_text(json.dumps(env,indent=2)+'\n')
print('Restored exact original env-J LEAN_PATH prefixes; run2 adds only this job private object directory.')
