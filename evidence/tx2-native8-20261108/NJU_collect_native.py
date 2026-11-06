from pathlib import Path
import json,re,hashlib
from NJU_read import read_text
E=Path(__file__).resolve().parent
pairs=[('decode_total',5,6),('field_canonical',7,8),('round0_window',17,18),('round1_window',19,20),('final_window',21,22)]
rows=[]
for name,positive,control in pairs:
 refs=[]
 for number,role in [(positive,'PASS'),(control,'matched FAIL')]:
  a=f'NJU_K{number:03d}';r=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());log=read_text(E/a/'stdout.log')
  assert r['exit_status']==(0 if role=='PASS' else 1)
  assert g['graph_matches_frozen'] and lock['unchanged']
  assert ('VERIFICATION:- SUCCESSFUL' if role=='PASS' else 'VERIFICATION:- FAILED') in log
  refs.append(dict(attempt=a,role=role,receipt=a+'/receipt.json',source_sha256=r['source_hashes']['NJU_src/crates/aspis-r1-cost-probe/src/NJU_finish.rs'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
 rows.append(dict(harness='weights::NJU_finish::'+name,positive=refs[0],control=refs[1],scope='one arbitrary field read, not a whole finish invocation'))
raw=[]
for name,p,c in [('noncanonical_no_return',13,14),('short_no_return',15,16),('round0_no_return',23,24),('round1_no_return',26,27),('final_no_return',28,30)]:
 refs=[]
 for num,is_control in [(p,False),(c,True)]:
  a=f'NJU_K{num:03d}';r=json.loads((E/a/'receipt.json').read_text());log=read_text(E/a/'stdout.log')
  checks=[dict(id=i,status=status,description=description,location=location) for i,status,description,location in re.findall(r'Check \d+: ([^\n]+)\n\s*- Status: ([^\n]+)\n\s*- Description: "([^\n]*)"\n\s*- Location: ([^\n]+)',log)]
  failed=[x for x in checks if x['status']=='FAILURE']
  continuation=[x for x in checks if ('weights::NJU_finish::bad_window::<' in x['id'] if name in ['round0_no_return','round1_no_return','final_no_return'] else x['id'].startswith('weights::NJU_finish::'+name+'.assertion.')) and 'placeholder message' in x['description']]
  assert len(continuation)==1 and continuation[0]['status']==('FAILURE' if is_control else 'SUCCESS'),(a,continuation)
  assert len(failed)==1,(a,failed)
  if not is_control:assert 'panic' in failed[0]['id'] or 'unwrap' in failed[0]['id'] or 'slice_index' in failed[0]['id']
  refs.append(dict(attempt=a,exit_status=r['exit_status'],full_kani_verdict='FAILED; expected abort property retained',continuation_property=continuation[0],failed_checks=failed,all_other_checks_pass_or_unreachable=True,checks=len(checks)))
 raw.append(dict(harness=name,classification='raw universal no-return property, NOT an exit-zero Kani pass; should_panic alone never credited',positive=refs[0],control=refs[1]))
(E/'NJU_NATIVE_CERTIFICATES.json').write_text(json.dumps(dict(rows=rows,raw_abort_components=raw,diagnostic_only=['NJU_K009','NJU_K010','NJU_K011','NJU_K012'],composition_status='TX2:115 generalized supplement candidate, component gates PASS; TX2:065 OPEN',transport='option-A P6/D188 reclassification',kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'),indent=2)+'\n')
print(json.dumps(dict(native_pairs=len(rows),raw_abort_pairs=len(raw),root_status='OPEN')))
