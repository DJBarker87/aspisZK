from NMX_formal import *
import json
steps=json.loads((E/'NMX_STEP_MANIFEST.json').read_text())
for row in steps:
 a=f"NMX_L{61+row['occurrence']:03d}"
 r=run(a,'lean',row['module'])
 if r['exit_status']:raise SystemExit(r['exit_status'])
