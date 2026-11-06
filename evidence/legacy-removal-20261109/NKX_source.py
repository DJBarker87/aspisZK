"""Independent AST extraction and frozen-source comparison utilities."""
from pathlib import Path
import sys,subprocess,json,hashlib
from functools import lru_cache
sys.dont_write_bytecode=True
sys.path.insert(0,'/private/tmp/NFZ-parser-20261104')
from tree_sitter import Language,Parser
import tree_sitter_rust
E=Path(__file__).resolve().parent; R=E.parents[1]; F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
parser=Parser(Language(tree_sitter_rust.language()));sha=lambda b:hashlib.sha256(b).hexdigest()
@lru_cache(maxsize=None)
def frozen(p):return subprocess.check_output(['git','show',F+':'+str(p)],cwd=R)
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def parse(b):
 root=parser.parse(b).root_node
 assert not root.has_error
 return root

@lru_cache(maxsize=None)
def funcs(p,b):
 out={}
 for n in walk(parse(b)):
  if n.type!='function_item' or n.child_by_field_name('body') is None:continue
  ancestors=[];a=n.parent
  while a:
   if a.type in ['mod_item','function_item','trait_item']:ancestors.append(b[a.child_by_field_name('name').start_byte:a.child_by_field_name('name').end_byte].decode())
   if a.type=='impl_item':
    t=a.child_by_field_name('type');ancestors.append(b[t.start_byte:t.end_byte].decode())
   a=a.parent
  name=b[n.child_by_field_name('name').start_byte:n.child_by_field_name('name').end_byte].decode();key=str(p)+'::'+'::'.join(ancestors[::-1]+[name]);body=n.child_by_field_name('body')
  # Preserve distinct same-target conversion impls by frozen input type where needed.
  if key in out:
   prior=out[key];duplicate=1
   while key+'@duplicate'+str(duplicate) in out:duplicate+=1
   out[key+'@duplicate'+str(duplicate)]=prior
  attrs=[];prev=n.prev_named_sibling
  while prev and prev.type=='attribute_item':attrs.append(b[prev.start_byte:prev.end_byte].decode());prev=prev.prev_named_sibling
  out[key]=dict(name=name,line=n.start_point.row+1,end=n.end_point.row+1,full=sha(b[n.start_byte:n.end_byte]),body=sha(b[body.start_byte:body.end_byte]),text=b[n.start_byte:n.end_byte],test=any('#[test]' in a for a in attrs))
 return out

def remove_nodes(b,nodes):
 spans=[]
 for n in nodes:
  start=n.start_byte;prev=n.prev_named_sibling
  while prev and prev.type in ['attribute_item','line_comment','block_comment']:
   start=prev.start_byte;prev=prev.prev_named_sibling
  spans.append((start,n.end_byte))
 for s,e in sorted(spans,reverse=True):b=b[:s]+b[e:]
 return b

if __name__=='__main__':
 paths=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'programs/aspis-pool'],cwd=R,text=True).splitlines();removed=[];changed=[];tests_before=[];tests_after=[];files=[]
 current={}
 for p in paths:
  if not p.endswith('.rs'):continue
  old=funcs(p,frozen(p));new=funcs(p,(R/p).read_bytes()) if (R/p).exists() else {};current.update(new)
  if not (R/p).exists():files.append(p)
  for k,v in old.items():
   if v['test']:tests_before.append(k)
   if k not in new:removed.append(dict(function=k,frozen_line=v['line'],test=v['test']))
   elif v['full']!=new[k]['full']:changed.append(dict(function=k,frozen_line=v['line'],old=v['full'],new=new[k]['full']))
  tests_after.extend(k for k,v in new.items() if v['test'])
 inv=json.loads((R/'evidence/pool-inventory-20261109/NKS_INVENTORY.json').read_text());rows={v['function']:v for v in inv['rows']+inv['off_review_rows']}
 roots=['programs/aspis-pool/src/'+p+'::'+n for p,n in [('pair_forest.rs','process_pair_forest_initialize_with_runtime_v1'),('pair_forest.rs','process_pair_forest_checkpoint_with_runtime_v1'),('pair_forest.rs','process_pair_forest_deposit_with_runtime_v1'),('pair_forest.rs','process_pair_forest_terminal_v1'),('pair_forest.rs','process_pair_forest_terminal_full_asf8_v1'),('pair_processor.rs','process_pair_private_transfer_with_verifier_v1'),('pair_processor.rs','process_pair_withdrawal_with_verifier_v1')]]
 # Refine only demonstrably spurious conservative name/callback alternatives.
 # Retain their complete incoming-edge evidence; do not silently drop rows.
 exclusions={
 'programs/aspis-pool/src/anchor.rs::PrevalidatedHistoricalAnchorV1::header':'AST callback overlay mistakes local RootPageHeaderV1 value header for function item; actual append_roots_unchecked argument is a record.',
 'programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::deref':'MIR conservative Deref name alternatives include unrelated Vec/Box/CanonicalPairPoolStateV1 receivers; retained sources never construct CanonicalPoolStateV1.',
 }
 for mod in ['cancel_prepared_settlement_instruction','prepared_settlement_format','prepared_settlement_instruction','settle_prepared_instruction']:
  exclusions['programs/aspis-pool/src/'+mod+'.rs::ProgramError::from']='Conservative From name alternatives; retained callers convert numeric/core/PoolInstruction errors, never this deleted prepared instruction error type.'
 excluded=[]
 for caller,row in rows.items():
  for edge in row['edges']:
   for target in edge['targets']:
    if target in exclusions:
     excluded.append(dict(caller=caller,target=target,reason=exclusions[target],edge=edge))
 # The conservative emitted inventory omitted cfg/off/inlined initialization
 # codec nodes. Add source-established dependencies explicitly, plus common
 # fixed-array codecs reached through unchanged pair encoders.
 source_added=['programs/aspis-pool/src/instruction.rs::'+n for n in ['decode_initialize_instruction_v1','encode_initialize_instruction_v1','encode_private_transfer_instruction_v1','encode_withdrawal_instruction_v1']]+['programs/aspis-pool/src/deposit_transport.rs::encode_deposit_instruction_v1']
 todo=roots[:]+source_added;seen=set()
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k);todo += [t for t in rows.get(k,{}).get('callees',[]) if t not in exclusions]
 checks=[];missing=[]
 for k in sorted(seen):
  p=k.split('::')[0];old=funcs(p,frozen(p)).get(k)
  if not old:continue
  new=current.get(k) if p.startswith('programs/aspis-pool/') else funcs(p,(R/p).read_bytes()).get(k)
  rec=dict(function=k,frozen_line=old['line'],direct_frozen_full_sha256=old['full'],direct_frozen_body_sha256=old['body'],inventory_full_sha256=rows.get(k,{}).get('full_function_sha256'),inventory_body_sha256=rows.get(k,{}).get('frozen_body_sha256'),current_full_sha256=new['full'] if new else None,identical=new is not None and new['text']==old['text'])
  if rec['inventory_full_sha256'] is not None:assert rec['inventory_full_sha256']==old['full'],rec
  if rec['inventory_body_sha256'] is not None:assert rec['inventory_body_sha256']==old['body'],rec
  checks.append(rec)
  if not rec['identical']:missing.append(rec)
 result=dict(frozen_revision=F,roots=roots,source_added_dependencies=source_added,conservative_inventory_checks=checks,nonidentical=missing,conservative_edge_refinements=excluded,changed_functions=changed,deleted_files=files,removed_functions=removed,tests_before=tests_before,tests_after=tests_after)
 (E/'NKX_BYTE_IDENTITY.json').write_text(json.dumps(result,indent=1)+'\n')
 assert not missing,missing
 assert all(v['function']=='programs/aspis-pool/src/processor.rs::process_instruction' for v in changed),changed
 print(json.dumps(dict(removed=len(removed),tests_before=len(tests_before),tests_after=len(tests_after),checks=len(checks),nonidentical=len(missing),changed=changed)))
