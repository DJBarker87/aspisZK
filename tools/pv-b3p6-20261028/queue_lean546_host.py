"""Sequential job-owned focused queue; stops on any refusal or proof failure."""
from pathlib import Path
import subprocess,json
from run import H
queue=['PV_B3P_LeadingSource546227','PV_B3P_CopySource546227','PV_B3P_ScheduleSource546227']
# No automatic resubmission: successful predecessors are retained by tally.
t=json.loads((H/'TALLY-resume18.json').read_text())
for module in queue:
 if any(r['module']==module and r['exit']==0 for r in t.get('receipts',[])):continue
 r=subprocess.run(['python3',str(H/'compile_resume18.py'),module])
 if r.returncode:raise SystemExit(r.returncode)
