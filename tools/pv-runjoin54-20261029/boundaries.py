"""Read-only before/after endpoint, frozen Rust and key-noninteraction record."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin54-20261029'
base='1adf3ca50f50b8983de4eeb9609731a1301ca463';head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
x=json.loads((R/'evidence/pv-runjoin41-20261028/endpoint-boundaries-unchanged.json').read_text());checks=[]
for p in x['paths']:
 before=subprocess.check_output(['git','show',base+':'+p],cwd=R);after=subprocess.check_output(['git','show',head+':'+p],cwd=R)
 assert before==after,p
 checks.append(dict(path=p,before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest(),byte_identical=True))
diff=subprocess.check_output(['git','diff',base,head,'--',*x['paths']],cwd=R,text=True);assert not diff
x.update(base=base,head=head,diff=diff,source_checks=checks)
(E/'endpoint-boundaries-unchanged.json').write_text(json.dumps(x,indent=2)+'\n')
rustdiff=subprocess.check_output(['git','diff','82566acdfb',head,'--','crates/','programs/','tools/r1-cost-probe'],cwd=R,text=True);assert not rustdiff
(E/'stage-A-source-identity.json').write_text(json.dumps(dict(base='82566acdfb',head=head,paths=['crates/','programs/','tools/r1-cost-probe'],diff=rustdiff,byte_identical=True,reused_evidence_scope='Historical stage-A source-identical artifacts only; no new ELF or native verification.',new_native_credit=False,wallet_or_account_keys_touched=False),indent=2)+'\n')
print('All endpoint/trust/observer/oracle statements and frozen Rust are unchanged')
