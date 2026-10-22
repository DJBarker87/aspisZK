#!/usr/bin/env python3
"""Adoption-only ownership and extraction overlay; source/hash work only."""
import runpy, json, re, collections
from pathlib import Path
N=runpy.run_path(str(Path(__file__).with_name('check.py')))
R,E,B=N['R'],N['E'],N['B'];sha=N['sha'];write=N['write'];git=N['git'];BASE=N['BASE'];TARGET=N['TARGET']
paths=['crates/aspis-r1-cost-probe/src/'+n+'.rs' for n in ['fast_dots','fast_pairing','weights']]
owners=json.loads((B/'s10-inventory2-20261021/mir-owners.json').read_text())
records=[]
for r in owners:
 if not any(p in r.get('span','') for p in paths):continue
 n=r['name'];changed=any(t in n for t in ['fast_dots::four_dots','canonical::Q::from_limbs','weights::powers'])
 removed=changed and 'closure#' in n
 records.append({**r,'old_owner':r['owner'],'new_owner':r['owner'],'pin_status':'HISTORICAL' if changed else 'unchanged body; old compiler span/instance identity historical', 'action':'remove superseded closure from adopted source inventory' if removed else 'regenerate compiler identity; retain owner, rebind changed body' if changed else 'retain semantic owner; re-record new source line/instance identity', 'acceptance':'proposal at generic source level; no deployed completeness claim'})
records.append({'name':'aspis_r1_cost_probe::fast_dots::four_dots_one','old_owner':None,'new_owner':'S4','pin_status':'NEW','action':'new single-slot helper, owned and proved by session A; do not reuse old closure ID','acceptance':'source declaration only; compiler ID must be regenerated'})
changed=[{'declaration':'aspis_r1_cost_probe::'+n,'old_owner':o,'new_owner':o,'consumers':c,'size':z} for n,o,c,z in [
 ('fast_dots::four_dots','S4',['S7 query_values','S4 TX1/TX2'],'one entry replaced plus one new single-slot helper; session A'),
 ('fast_pairing::canonical::Q::from_limbs','S5',['checked_q','EbyKDot::push (S8)'],'one fixed four-U32 Option predicate; closure removed; no field multiplication'),
 ('weights::powers','S3',['Prepared kappa N=7 (S1)','gamma N=29 (S1/S4/S7 callers)','Weights N=4 (S3/S9)'],'one generic N while-loop; zero-length exit and N>0 early final exit; N-1 multiplies, previously N')]]
write('ownership.json',{'target_revision':TARGET,'inputs':{'mir-owners.json':sha((B/'s10-inventory2-20261021/mir-owners.json').read_bytes()),'owner-lowering.json':sha((B/'s10-inventory4-20261021/owner-lowering.json').read_bytes())},'changed_declarations':changed,'records':records,'scope':'Recomputed source-owner overlay, retains single existing S3 ownership of generic powers and records shared consumers rather than double ownership. S5 owns canonical constructor; S8 owns EbyKDot. Old anonymous closure/constant/instance IDs and ELF address edges are not adopted IDs.','complete':False})
texts=[]
sourcepaths=[p for p in (R/'crates/aspis-r1-cost-probe/src').glob('*.rs')]+list((R/'crates/aspis-core/src').rglob('*.rs'))
sources={str(p.relative_to(R)):p.read_text() for p in sourcepaths}
for scope in ['repin-s7-20261020','repin-s8-20261020']:
 p=B/scope/'llbc-declarations.json'
 for d in json.loads(p.read_text()):
  s=d.get('source_text');
  if not s:continue
  matches=[p for p,t in sources.items() if s in t]
  texts.append({'receipt':str(p.relative_to(R)),'id':d['id'],'name':d['name'],'source_text_sha256':sha(s.encode()),'current_matches':matches,'status':'unchanged exact source text' if matches else 'HISTORICAL; source text not present','has_body':d.get('has_body',d.get('body_tag'))})
write('extraction-text.json',{'target_revision':TARGET,'declarations':texts,'note':'Exact retained source_text membership checked; opaque callees remain opaque. This does not re-extract LLBC or infer cfg/toolchain equality.'})
# Record all source/model modules participating in frozen2 and lead-cone joins.
model=[]
for p in sorted((R/'docs/research/100bit-spend-path-20261013/lean').glob('*.lean')):
 if not p.name.startswith(('OraclePortFrozen2','OraclePortHeadlineFrozen2','Frozen2Start','OraclePortS10','S7','S8','MultiproofCone','OraclePortCkptAbi','Checkpoint')):continue
 rel=str(p.relative_to(R));data=p.read_bytes()
 assert git('show',TARGET+':'+rel)==data
 matching=[r for r in N['checks'] if r['path']==rel and r['status']=='unchanged']
 model.append({'path':rel,'sha256':sha(data),'target_text_identity':True,'retained_matching_receipts':sorted({s for r in matching for s in r['receipts']})})
write('model-pins.json',{'target_revision':TARGET,'modules':model,'note':'Exact checkout/target identity and matching retained pins; theorem statements unchanged here. No new compilation, axioms audit, source instance or premise removal.'})
identity=B/'s4-combined-standing-retained-v2-20261021/receipts/id-slot-check/identity-task/receipts/identity/identity.json'
idata=json.loads(identity.read_text())
old={'default':'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','devnet':'fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
new={k:v['sha256'] for k,v in idata['artifacts'].items()};new['pool']=old['pool']
references=[]
for scope in N['scopes']:
 for p in sorted(scope.rglob('*')):
  if not p.is_file() or p.suffix not in ['.json','.md','.txt','.sha256'] or p.stat().st_size>12000000:continue
  s=p.read_text(errors='replace')
  for k,h in old.items():
   if h in s:references.append({'receipt':str(p.relative_to(R)),'artifact':k,'old_sha256':h,'new_sha256':new[k],'status':'unchanged retained Pool artifact pin' if k=='pool' else 'HISTORICAL verifier artifact; old graph/CFG/symbol certificate not transferred'})
write('artifact-pins.json',{'target_revision':TARGET,'identity_receipt':str(identity.relative_to(R)),'identity_receipt_sha256':sha(identity.read_bytes()),'old':old,'new':new,'references':references,'new_default_devnet_size':1508152,'pool_size':605704,'note':'Adopted pins reused from approved identity receipt/C3 addendum. No ELF bytes locally rehashed or rebuilt. All old verifier address/inline/call-graph evidence remains historical, including linked.elf/debug comparisons; Pool pin alone does not validate changed verifier callees.'})
print(json.dumps({'owner_records':len(records),'source_text_checks':len(texts),'source_text_missing':sum(not r['current_matches'] for r in texts),'model_modules':len(model),'binary_references':len(references)},indent=2))
