"""Additional mandatory native target-isolation check; existing NFK is unchanged."""
from pathlib import Path
import json,hashlib,subprocess,time,resource,sys,copy
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107';start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda n:json.loads((E/n).read_text());put=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
fail=[]
for p in sorted(E.glob('NIJ_K???.json')):
 x=json.loads(p.read_text());cmd=x.get('native_command',[]);target=cmd[cmd.index('--target-dir')+1] if '--target-dir' in cmd else None
 if target is None or not target.startswith(B+'/NIJ_'):fail.append(dict(attempt=x['attempt'],target=target,config_sha256=sha(p.read_bytes()),reason='Native build output is outside own NIJ workspace'))
assert len(fail)==120
# Preserve exact previous candidate artifacts once; rerunning is idempotent.
w=E/'NIJ_WITHHELD_ARTIFACTS.json'
if not w.exists():put(w.name,{n:read(n) for n in ['NIJ_CLOSED.json','NIJ_LEDGER_DELTA.json','NIJ_EDGES.json']})
prior=read(w.name);assert prior['NIJ_CLOSED.json']['new_composed_rows']==3
put('NIJ_NATIVE_ISOLATION.json',dict(status='FAIL_NATIVE_OUTPUT_ISOLATION',cases=fail,source_and_lock_checks_unchanged=True,proof_verdicts_preserved=True,new_credit_withheld=True,reason='All native configs inherited predecessor NHY_target. Native outputs may have modified that predecessor build directory. No source/worktree or frozen file was intentionally modified there; no forensic claim of byte-identical artifacts. Do not delete/change predecessor target. Corrected OWN runner explicitly selects B/NIJ_target with prefix assertion; no more native budget, no rerun performed. Lead review needed before any reuse of prior candidates.',lead_infrastructure_edited=False,keys_touched=False))
d=copy.deepcopy(prior['NIJ_LEDGER_DELTA.json']);d.update(new_closed_rows=[],rows=[],whole_ledger_counts_after_inherited_and_new=dict(CLOSED=363,OPEN=236,QUALIFIED=0),withheld_rows=['TX2:202','TX1:NGB001','TX2:211'],withheld_reason='FAIL_NATIVE_OUTPUT_ISOLATION',withheld_candidate_artifacts=w.name)
d['checks_added']+=['native output target must lie inside own NIJ workspace; all120 old configurations denied, three previously validated candidates withheld'];put('NIJ_LEDGER_DELTA.json',d)
put('NIJ_CLOSED.json',dict(schema_version=1,frozen_revision=prior['NIJ_CLOSED.json']['frozen_revision'],new_composed_functions=0,new_composed_rows=0,functions=[],driver_root_status='OPEN',withheld_candidates=w.name,reason='Additional native target isolation gate fails; no new row credit'))
put('NIJ_EDGES.json',dict(edges=[],no_out_of_slice_credit=True,withheld_candidate_edges=w.name))
a=read('NIJ_AUDIT.json');a.update(formal_status='PASS_AX2_NFX',admission_status='DENIED_NATIVE_OUTPUT_ISOLATION',native_isolation='NIJ_NATIVE_ISOLATION.json');put('NIJ_AUDIT.json',a)
put('NIJ_ISOLATION_VALIDATION.json',dict(target='strict native output ownership gate and conservative admission withdrawal',exit_status=0,gate_status='DENIED',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A policy gate',new_closed_rows=0,all_native_configs_denied=len(fail)))
print('PASS conservative isolation gate: 0 new CLOSED; 3 withheld candidates')
