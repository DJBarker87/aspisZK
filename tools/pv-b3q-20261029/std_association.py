"""Statement-by-statement own-1 dossier for the seven compiled standard rows."""
from pathlib import Path
import json,lzma,re,hashlib
D=Path('evidence/pv-b3q-20261029');B=Path('evidence/pv-b3p6-20261028')
comp=json.loads((B/'std227-comparison-stdcone-resume5.json').read_text());capture=json.load(lzma.open(B/'std227-stdcone-resume5.json.xz','rt'))
expected={5:('result_branch','{ match self { Ok(v) => ControlFlow::Continue(v), Err(e) => ControlFlow::Break(Err(e)), } }'),56:('u32_unwrap_or','{ match self { Some(x) => x, None => default, } }'),57:('u32_is_some','{ matches!(*self, Some(_)) }'),70:('u32_u64','{ small as Self }'),117:('bool_u32','{ small as u8 as Self }'),118:('u16_usize','{ small as Self }'),119:('u8_usize','{ small as Self }')}
tokens=lambda s:re.findall(r'\w+|=>|::|[^\s]',re.sub(r'//[^\n]*','',s))
caller=Path('tools/pv-b3p6-20261028/v244/host_terminal.rs').read_text();assert 'public.withdrawal_amount.unwrap_or(0)' in caller and 'public.withdrawal_amount.is_some()' in caller
rows=[]
for ident,(name,body)in expected.items():
 r=next(r for r in comp['rows']if r['id']==ident);assert tokens(r['deployed']['body'])==tokens(body),(name,r['deployed']['body'])
 f=capture['files'][r['file']]['deployed'];assert hashlib.sha256(f['text'].encode()).hexdigest()==f['sha256'];assert r['deployed']['item']in f['text']
 steps={
 'result_branch':['consume Result discriminant','Ok: move v into Continue(v)','Err: move e into Err(e), then Break; no conversion/drop','return outer ok; no store, allocation, panic or abort'],
 'u32_unwrap_or':['read/move Option<u32> discriminant','Some: return copied u32 payload; unused fallback is Copy, drop is empty','None: return fallback; Option has no payload destructor','no mutation, allocation, error or abort'],
 'u32_is_some':['shared immutable borrow; retain its storage','matches! expands to Some(_)=>true, None=>false','only discriminant observed; no store/drop/error/abort'],
 'bool_u32':['cast Bool to u8 (false=0, true=1)','zero-extend u8 to u32','return; no control flow/store/drop/error/abort'],
 }.get(name,['zero-extend small into destination width','return; no branch/store/drop/error/abort'])
 rows.append(dict(name=name,capture_declaration_id=ident,file=r['file'],source_path=f['path'],source_file_sha256=f['sha256'],source_body_sha256=hashlib.sha256(r['deployed']['body'].encode()).hexdigest(),source_item=r['deployed']['item'],source_signature=r['signature'],steps=steps,lemma='PV_B3Q_Std.binding_'+name,existing_link='PV_B3P_Groups14227.PV_B3P_Link_std_dependency_closure14',evidence_class='structural own-1',compiler_boundary='V370 / pending D381,D386 retained',macro_context=r['deployed']['context']))
# Conservative source union. It is explicitly NOT an omission certificate.
union={}
for p in sorted(B.glob('std227-comparison-*-resume5.json')):
 x=json.loads(p.read_text())
 for r in x['rows']:
  key=json.dumps([r['file'],r['name'],r.get('deployed',{}).get('item'),r.get('deployed',{}).get('context'),r.get('signature')],sort_keys=True)
  if key not in union:union[key]=dict(name=r['name'],file=r['file'],source_status=r['status'],source_body_sha256=hashlib.sha256(r.get('deployed',{}).get('body','').encode()).hexdigest(),inventories=[],binding_status='OPEN: concrete model and source-step binding required')
  union[key]['inventories'].append(dict(path=str(p),id=r['id']))
for r in union.values():
 matches=[row for row in rows if any(z['id']==row['capture_declaration_id']and z['path'].endswith('std227-comparison-stdcone-resume5.json')for z in r['inventories'])]
 if matches:r['binding_status']='own-1 instance compiled for documented carrier';r['lemmas']=[x['lemma']for x in matches]
out=dict(evidence_class='structural own-1 for seven documented rows only',bodies=rows,conservative_source_union=list(union.values()),complete_reached_cone=False,remaining_coverage=['pre-inline array/slice/pointer source','Vec and allocation paths reached through fields/frontier','dependency bodies and generated glue','panic formatting and abort source paths; prior panic-only classification retained'],no_new_trust_items=True)
(D/'std-source-association.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(bound_rows=len(rows),conservative_union=len(union),complete_reached_cone=False)))
