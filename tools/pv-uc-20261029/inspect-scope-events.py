"""Read-only user-bus subscribe/Ping/unsubscribe check. No scope or timing run."""
from pathlib import Path
import hashlib,json,shlex,subprocess
R=Path(__file__).resolve().parents[2];p=R/'tools/pv-uc-20261029/timing-window-guard.py'
program=p.read_text().split("if __name__=='__main__':",1)[0]+'''
events=None
try:
 events=ScopeEvents().start();events.sync()
 result=dict(status='PASS read-only subscription and queue-drain API check',own_unit=events.own_unit,events=events.history,capped_scopes_started=0,prover_calls=0,timing_samples=0)
except BaseException as exc:
 result=dict(status='FAIL',error=repr(exc),capped_scopes_started=0,prover_calls=0,timing_samples=0)
finally:
 if events:events.close()
print(json.dumps(result))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(program)],capture_output=True,text=True)
x=dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,guard_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
if r.returncode==0:x['result']=json.loads(r.stdout)
(R/'evidence/pv-uc-20261029/timing-scope-subscription-inspection.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x,indent=2))
assert r.returncode==0 and x['result']['status'].startswith('PASS')
