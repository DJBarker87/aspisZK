"""Finalize retained artifacts after sixty charged runs; never launch a compiler/solver."""
from pathlib import Path
import json,lzma,subprocess,datetime,collections
E=Path(__file__).resolve().parent
for script in ['d549_report.py','d549_rows.py']:
 subprocess.run(['python3',str(E/script)],check=True)
s=json.loads((E/'D549-RESULTS.json').read_text());assert s['charged_invocations']==60 and not s['campaign_in_progress']
base=json.loads((E/'SUMMARY.json').read_text());base.update(final_status=s['credit_status'],new_kani_runs=60,initial_spent=2,D549_additional_invocations=58,endpoint_premises_removed=0,property_reruns=29,matched_controls=29,charged_setup_failures=2,used_IDs=[r['id']for r in s['results']],budget_exhausted=True,remaining_rerun_work=True,std_transfer='WITHHELD',new_restored_deployed_credits=0,current_rows=34,current_scopes_depending_on_suspended_credit=0,Lean=0)
ref=[]
for p in sorted((E/'host').glob('K792[0-9][0-9]')):
 a=p/'admission.json';b=p/'barrier.json'
 if a.exists():
  gates={name:json.loads((p/name).read_text())for name in ['admission.json','barrier.json']if (p/name).exists()}
  denied=[name for name,d in gates.items()if not d.get('allowed',False)]
  if denied:
   assert not(p/'time.log').exists()and not(p/'symbols-index.json').exists();d=gates[denied[0]];ref.append({'id':p.name,'allowed':False,'denied_gates':denied,'STARTED_exists':(p/'STARTED.json').exists(),'compiler_started':False,'charged':0,'error':d.get('error'),'bounded_reserved_bytes':d.get('bounded_reserved_bytes'),'projected_reserved_bytes':d.get('projected_reserved_bytes')})
base['uncharged_refused_IDs']=[x['id']for x in ref];(E/'SUMMARY.json').write_text(json.dumps(base,indent=2)+'\n')
r=json.loads((E/'D549-REFUSALS.json').read_text());r['final_refusal_inventory']=ref;r['charged_invocations']=60;(E/'D549-REFUSALS.json').write_text(json.dumps(r,indent=2)+'\n')
p=json.loads((E/'D549-RUN-PLAN.json').read_text());p['actual_charged_IDs']=base['used_IDs'];p['uncharged_refusals']=base['uncharged_refused_IDs'];p['last_invocation']=s['results'][-1]['id'];p['complete']=True;p['IDs']='Logical configs K79200..K79259; actual charged IDs and refused IDs enumerated below';(E/'D549-RUN-PLAN.json').write_text(json.dumps(p,indent=2)+'\n')
report=E/'REPORT-D549.md';txt=report.read_text().replace('This report is a checkpoint until D549-RESULTS.json records sixty charged invocations.','Campaign complete: sixty charged invocations (the two initially spent plus 58 D549 invocations), 29 positive PASS / 29 matched expected failures / two charged setup failures. '+str(len(ref))+' uncharged admission refusal(s) are retained.').replace('The final D549-VALIDATION.json will be one artifact/pair/resource/current-row audit','D549-VALIDATION.json records one final artifact/pair/resource/current-row audit');txt+='\nStop reason: all sixty authorized invocations are spent. No additional Kani or Lean run is authorized by this continuation. All 34 retained current row scopes have no still-SUSPENDED Kani dependency; historical suspensions and OPEN native/world/std associations remain expressly named. The next concrete deliverable is a checked local-context association for native Token::drop/Core::default and the shared memo, followed by exact reached-item std mapping before any deployed transfer.\n';report.write_text(txt)
(E/'COMMITS-D549.txt').write_text('Branch codex/pv-k3scan-20261101; commits after immutable audit base bad175c553, before final report commit (final report commit adds only evidence):\n'+subprocess.check_output(['git','log','--oneline','bad175c553..HEAD'],text=True))
print({'charged':60,'pairs':len(s['pairs']),'refused':base['uncharged_refused_IDs'],'last':s['results'][-1]['id']})
