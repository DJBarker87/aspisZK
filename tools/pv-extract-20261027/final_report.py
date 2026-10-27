from pathlib import Path
import json,re,collections,subprocess,hashlib
E=Path('evidence/pv-extract-20261027');t=json.loads((E/'TALLY.json').read_text());rs=[]
for p in sorted(E.glob('424*.json')):
 if not re.fullmatch(r'424\d\d.json',p.name):continue
 r=json.loads(p.read_text());time=r['time_log']
 def m(label):
  x=re.search(r'^\s*'+re.escape(label)+r':\s*(.*)$',time,re.M);return x[1] if x else None
 r.update(wall=m('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_kib=m('Maximum resident set size (kbytes)'),swap=m('Swaps'))
 if not r['axioms']:r['print_axioms_result']='N/A: module contains types/explicit parameters only, no theorem' if r['exit']==0 else 'Failed compile; any diagnostic sorryAx is rejected, not an accepted result'
 else:r['print_axioms_result']='\n'.join(r['axioms'])
 rs.append(r)
assert len(rs)==t['lean_charged']==60
accepted=[r for r in rs if r['exit']==0];bad=[]
for r in accepted:
 for line in r['axioms']:
  if 'sorryAx' in line or not all(x in ['propext','Classical.choice','Quot.sound'] for x in re.search(r'\[(.*)\]',line)[1].split(', ')):bad.append([r['attempt'],line])
assert not bad
last=json.loads((E/'42460.json').read_text());report=dict(branch='codex/pv-extract-20261027',base='7599dff5b274d52324ae8681664f6b343f9a81ac',compiled_final_revision=last['source_revision'],lean_attempts=60,passed=sum(r['exit']==0 for r in rs),failed=sum(r['exit']!=0 for r in rs),kani=0,next_unused_id=t['next_env_j_id'],uncharged_id=42439,uncharged_reason='Missing dependency object in local preflight; no scope/compiler invoked, ID retained as consumed',final_target=last['module'],final_axiom_outputs=len(last['axioms']),accepted_axioms=['propext','Classical.choice','Quot.sound'],forbidden_axioms=[],shipped_source_changes=False,source_row_laws_added=0,endpoint_premises_removed=0,retained=['V240/op223 source law','V164 P_source_p6','V164 P_proof_bytes','V164 reservation equation','prover/shipped association, E1/E2, real RunJoin, L1/L2/L3, client route and full privacy closure'],before_after='No endpoint or deployment premise removed, added, changed, weakened, or folded into trust.',all_lean_receipts=rs)
(E/'FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
(E/'RECEIPT-CORRECTIONS.md').write_text('''# Receipt interpretation

The command arrays are authoritative. `run_host.py` originally used a generic phase label saying the private preflight was removed for every Aeneas command. That description applies only to diagnostic commands using `pipeline/base/src/_build/default/main.exe`. The index-compress and index-closed Aeneas commands use `/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas`, SHA256562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19, with the guard enabled. Historical JSON is preserved; this note corrects the label without changing any command, result or hash.

The source revision in native run targets is the frozen worktree base, identifying unchanged shipped inputs. Candidate probe Rust is an uncommitted host-only proposed leaf, archived by `route-ii-op223.patch` and `extra-input-hashes.json`; it is not attributed to that frozen shipped revision. Every Lean submission records actual HEAD plus exact changed source hash and dependency object hashes. Final42460 compiled the fully committed5900139500b1fc0240ef3f9cc561c078411b7557 snapshot. `FINAL.json` normalizes each Lean receipt's GNU time fields. Parent/child GNU max RSS is not a sampled aggregate RSS. Cgroup memory.peak is separately recorded only where measured.

Env-J42439 was consumed by the local driver's missing-object preflight, with zero compiler invocations/zero budget charge. There were no reservation/quiet-window refusals. IDs42400–42460 are never reusable. Final54 passes/6 failed compiles exhaust60. Failed partial elaborations can print sorryAx; none is accepted or imported by the successful final target. Accepted sources contain no placeholder proof constructs.
''')
print(report['passed'],report['failed'],t['next_env_j_id'])
