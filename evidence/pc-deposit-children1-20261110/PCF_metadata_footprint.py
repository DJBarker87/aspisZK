"""Exact frozen-body / metadata-only source association for account predicates."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;xs=json.loads((E/'PCF_SOURCE_SLICES.json').read_text())
expected={
 'POOL:364':{'payer':{'is_signer','is_writable','executable','owner'},'system_program_account':{'key','owner','executable','is_signer','is_writable'}},
 'POOL:365':{'account':{'key','executable','is_signer','is_writable','owner'}}}
out=[]
for rid,params in expected.items():
 r=next(v for v in xs if v['row']==rid);s=r['text'];body=s[s.index('{'):s.rindex('}')+1]
 assert hashlib.sha256(body.encode()).hexdigest()==r['body_sha256']
 def check(text):
  found={p:set(re.findall(r'\b'+re.escape(p)+r'\s*\.\s*([A-Za-z_][A-Za-z0-9_]*)',text)) for p in params}
  return found==params and not any(k in text for k in ['try_borrow','borrow_mut','set_return_data','msg!','invoke','unsafe'])
 assert check(body)
 rejected=[]
 for name in params:
  for field in ['data','lamports','rent_epoch']:
   mutant=body[:-1]+f' let _ = {name}.{field}; }}'
   assert not check(mutant);rejected.append(name+'.'+field)
 out.append(dict(row=rid,source_body_sha256=r['body_sha256'],observed_fields={k:sorted(v) for k,v in params.items()},unobserved_native_cells='data,lamports,Rc/RefCell borrow counters; no payload/length/rent_epoch reads',mutation_controls_rejected=rejected,association='All observed flags/key/owner values are symbolic in the actual contract harness; SDK IDs independently checked by K013/K014. Valid live unobserved cells are preserved under the explicit empty modifies contract. Alias constructor controls K021/K022 use the SAME data/lamports RefCells. The frozen source has no branch depending on unobserved cells, so no empty-data or zero-borrow-counter caller clause is introduced.',review='P6 source/argument association; mathematical full-state result is PCF_Payer/PCF_Token.result_state_effects, not an added axiom'))
(E/'PCF_METADATA_FOOTPRINT.json').write_text(json.dumps(out,indent=1)+'\n');print('PCF metadata footprints exact; all unobserved-field mutations rejected')
