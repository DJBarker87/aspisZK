"""Three reserved focused axiom audits, sequential and admission-gated."""
from pathlib import Path
import subprocess,json,time,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin45-20261028'
for a,m in [(61297,'R1Z.PV_RunJoin_CoefficientAudit45'),(61298,'R1Z.PV_RunJoin_WeightPrerequisiteAudit45'),(61299,'R1Z.PV_RunJoin_SourceAudit45')]:
 for retry in range(11):
  deadlines=[json.loads(p.read_text())['epoch']+180 for p in E.glob('refusal-*.json')]
  deadline=max(deadlines,default=0)
  while time.time()<deadline:
   print('AUDIT COOLDOWN',a,round(deadline-time.time(),1),flush=True);time.sleep(min(45,deadline-time.time()))
  r=subprocess.run([sys.executable,str(R/'tools/pv-runjoin45-20261028/compile.py'),str(a),'0',m],cwd=R)
  if r.returncode==0:break
  if r.returncode not in (77,78):raise SystemExit(r.returncode)
  if retry==10:raise SystemExit(78)
