"""Append the capacity-recovery moving-head review; no compiler or proof launches."""
import collections,copy,json,pathlib,re,subprocess
E=pathlib.Path(__file__).resolve().parent
get=lambda *args:subprocess.check_output(['git',*args],text=True)
old=json.loads((E/'heads-end.json').read_text());heads={r:get('rev-parse',r).strip() for r in old};deltas=[];success=[]
for ref,new in heads.items():
 paths=get('diff','--name-only',old[ref],new).splitlines() if new!=old[ref] else []
 entry=dict(ref=ref,before=old[ref],after=new,paths=paths,successful_outputs=[])
 for p in paths:
  if not p.startswith('evidence/') or not p.endswith(('.log','.txt','.json','.md')):continue
  try:t=get('show',f'{new}:{p}')
  except subprocess.CalledProcessError:continue
  if 'Checking harness ' in t and re.search(r'VERIFICATION(?::-|:)?.*SUCCESSFUL',t):
   x=dict(ref=ref,revision=new,path=p,blob=get('rev-parse',f'{new}:{p}').strip(),harnesses=re.findall(r'Checking harness (.+?)\.\.\.',t))
   success.append(x);entry['successful_outputs'].append(x)
 deltas.append(entry)
assert len(success)==1 and success[0]['harnesses']==['padding_coordinate_gate::padding_events_coordinate']
s=json.loads((E/'scan.json').read_text());x=success[0];receipt=x['path'].replace('output.log','receipt.json');rv=json.loads(get('show',f"{x['revision']}:{receipt}"))
if not any(p['pass_output_blob']==x['blob'] for p in s['passes']):
 p=copy.deepcopy(next(p for p in s['passes'] if p['harness']=='sha256_default_snapshot' and 'dlib' in p['receipt']))
 p.update(harness=x['harnesses'][0],pass_output=x['path'],pass_output_blob=x['blob'],receipt=receipt,receipt_blob=get('rev-parse',f"{x['revision']}:{receipt}").strip(),command=rv['target'],source_revision=rv['source_revision'],ledger_rows=['V234','V235'],ledger_relation='Supporting padding/finalize proposal only; recount6 V234/V235 remain OPEN. No claimed original-row closure.',copy_builtin_reached=None,property_depends_on_copy=None,exemption=None,status='UNRESOLVED',reason='New PASS after prior handoff. Owner PLAN explicitly suspends this copy-dependent gate under ruling(r). Source callback copies 64 bytes into events and asserts event coordinates; no corresponding goto/trace recovered by this scan. No exemption or credit; ten-run diagnostic budget already exhausted.',diagnostic=None)
 p['tool_pins']['output_version_lines']=[l for l in get('show',f"{x['revision']}:{x['path']}").splitlines() if 'Kani Rust Verifier' in l]
 i=len(s['passes']);s['passes'].append(p);s['unresolved'].append(i)
 for r in s['row_consequences']:
  if r['row'] in p['ledger_rows']:r['supporting_passes'].append(i)
s['pass_count']=len(s['passes']);s['counts']=dict(collections.Counter(p['status'] for p in s['passes']));s['recovery_heads']=heads;s['recovery_review']='resume-review.json';s['coverage']+=' Capacity-recovery delta adds one unadjudicated dlib padding PASS; see resume-review.json.'
(E/'scan.json').write_text(json.dumps(s,indent=2)+'\n')
(E/'resume-review.json').write_text(json.dumps(dict(recovered_commit='6a392ecd4a',budget_used_before_resume=dict(kani=10,lean=0),additional_attempts=dict(kani=0,lean=0,native=0),heads=heads,deltas=deltas,new_pass_count=len(success),suspended_rows=s['suspended_rows'],unresolved=len(s['unresolved']),status='INCOMPLETE: diagnostic budget exhausted; no credit restored'),indent=2)+'\n')
