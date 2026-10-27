"""Focused requested-cohort checks; retain failures and continue independent targets."""
import subprocess,pathlib,json,sys
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7'
for a,m in enumerate(['ProverRwSuccessHashes','PV_CB_Merkle','PV_CB_Op84Exact','PV_CB_CandidateDictionary','PV_CB_CandidateCore','PV_RE_InstalledOp84'],39409):
 r=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume7-check.py'),str(a),'R1Z/'+m],capture_output=True,text=True)
 p=E/f'receipt-{a}.json'
 if not p.exists():print(r.stdout+r.stderr,flush=True);sys.exit(r.returncode or 2)
 d=json.loads(p.read_text());print(json.dumps({k:d.get(k) for k in ['attempt','target','exit','accepted']}),flush=True)
 if not d['accepted']:print(r.stdout[-1500:]+r.stderr[-500:],flush=True)
 if d['exit'] is None:sys.exit(2)
