#!/usr/bin/env python3
"""Frozen-source AST inventory; no compiler/prover execution. See report for limits."""
import sys, subprocess, json, hashlib, re, tomllib
from pathlib import Path
sys.path.insert(0,'/private/tmp/NBI1_python')
from tree_sitter import Language, Parser
import tree_sitter_rust
OUT=Path(__file__).parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
parser=Parser(Language(tree_sitter_rust.language()))
def git(*args): return subprocess.check_output(['git',*args])
def sha(b): return hashlib.sha256(b).hexdigest()
paths=[x for x in git('ls-tree','-r','--name-only',REV,'crates','programs').decode().splitlines() if '/src/' in x and x.endswith('.rs') and not re.search(r'(test|fixture|original|eight_way|prover)',x)]
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
files={}
for p in paths:
 proc.stdin.write((REV+':'+p+'\n').encode());proc.stdin.flush();h=proc.stdout.readline();n=int(h.split()[2]);files[p]=proc.stdout.read(n);proc.stdout.read(1)
proc.stdin.close();proc.wait()
# Feature union of the three release artifacts (Pool adds pool-adapter only).
features={'custom-heap','pool-adapter','private-leaf-salts','optimized-terminal','program-build','r0','pool-v1-kernel'}
for manifest in ['crates/aspis-r1-cost-probe/Cargo.toml','crates/aspis-statement/Cargo.toml']:
 spec=tomllib.loads(git('show',REV+':'+manifest).decode()).get('features',{})
 changed=True
 while changed:
  old=set(features)
  for k in list(features):
   features.update(x.split('/')[-1] for x in spec.get(k,[]) if not x.startswith('dep:'))
  changed=old!=features

def cfg_value(s):
 s=s.strip()
 m=re.match(r'^(any|all|not)\((.*)\)$',s,re.S)
 if m:
  op,inner=m.groups();parts=[];depth=0;start=0
  for i,c in enumerate(inner):
   if c=='(':depth+=1
   elif c==')':depth-=1
   elif c==',' and depth==0:parts.append(inner[start:i]);start=i+1
  parts.append(inner[start:]);vs=[cfg_value(x) for x in parts if x.strip()]
  return any(vs) if op=='any' else all(vs) if op=='all' else not vs[0]
 m=re.match(r'feature\s*=\s*"([^"]+)"',s)
 if m:return m[1] in features
 if s in ('test','kani','debug_assertions'):return False
 if s in ('target_os = "solana"','target_os="solana"'):return True
 return False

def disabled(node,b):
 prev=node.prev_named_sibling
 while prev is not None and prev.type in ('attribute_item','line_comment','block_comment'):
  if prev.type=='attribute_item':
   a=b[prev.start_byte:prev.end_byte].decode();m=re.match(r'#\[cfg\((.*)\)\]',a,re.S)
   if m and not cfg_value(m[1]):return True
  prev=prev.prev_named_sibling
 return False
funcs={};nodes={}
def walk(n):
 if disabled(n,b):return
 yield n
 for c in n.named_children:yield from walk(c)
for p,b in files.items():
 tree=parser.parse(b)
 def visit(n,owners=(),off=False):
  off=off or disabled(n,b)
  if off:return
  if n.type=='impl_item':
   typ=n.child_by_field_name('type');owners=owners+(b[typ.start_byte:typ.end_byte].decode(),)
  elif n.type=='mod_item':
   name=n.child_by_field_name('name');owners=owners+(b[name.start_byte:name.end_byte].decode(),)
  if n.type=='function_item':
   name=n.child_by_field_name('name');body=n.child_by_field_name('body')
   if body is None:return
   name=b[name.start_byte:name.end_byte].decode();owner='::'.join(owners)
   key=p+'::'+(owner+'::' if owner else '')+name+'@'+str(n.start_point.row+1)
   calls=[];loops=[];mut=[];field=[];digest=[]
   for c in walk(body):
    t=b[c.start_byte:c.end_byte].decode()
    if c.type=='call_expression':
     f=c.child_by_field_name('function');expr=b[f.start_byte:f.end_byte].decode();calls.append({'expression':expr,'line':c.start_point.row+1})
     if re.search(r'(?:digest|hashv|hash_with|absorb|block)\b',expr):digest.append(expr)
     if re.search(r'\b(mul|mul_m31|mul_qm31|add|sub|inv|square|double|reduce_u64|neg|pow)\b',expr):field.append(expr)
    if c.type in ('for_expression','while_expression','loop_expression'):loops.append({'line':c.start_point.row+1,'head':t.split('{')[0].strip()})
    if c.type=='reference_expression' and t.startswith('&mut'):mut.append({'line':c.start_point.row+1,'expression':t[:180]})
   funcs[key]={'id':key,'file':p,'line':n.start_point.row+1,'end_line':n.end_point.row+1,'name':name,'owner':owner,'body_byte_range':[body.start_byte,body.end_byte],'function_byte_range':[n.start_byte,n.end_byte],'body_sha256':sha(b[body.start_byte:body.end_byte]),'function_sha256':sha(b[n.start_byte:n.end_byte]),'calls':calls,'loops':loops,'mutable_borrows':mut,'mutable_signature': '&mut' in b[n.start_byte:body.start_byte].decode(),'field_arithmetic':sorted(set(field)),'oracle_digest_calls':sorted(set(digest))}
   nodes[key]=(n,body,b)
   for c in body.named_children:
    if c.type=='function_item':visit(c,owners+(name,),off)
   return
  for c in n.named_children:visit(c,owners,off)
 visit(tree.root_node)
# index_type! expands these two reached FibreIndex methods; retain template bytes.
mp='crates/aspis-core/src/r0/domain.rs';mb=files[mp]
for mn in ('new','get'):
 m=re.search(rb'pub (?:const )?fn '+mn.encode()+rb'\b',mb);start=m.start();op=mb.index(b'{',start);depth=1;end=op+1
 while depth:
  depth+=(mb[end]==123)-(mb[end]==125);end+=1
 line=mb[:start].count(b'\n')+1;k=mp+'::FibreIndex::'+mn+'@'+str(line)
 funcs[k]={'id':k,'file':mp,'line':line,'end_line':mb[:end].count(b'\n')+1,'name':mn,'owner':'FibreIndex','body_byte_range':[op,end],'function_byte_range':[start,end],'body_sha256':sha(mb[op:end]),'function_sha256':sha(mb[start:end]),'calls':[],'loops':[],'mutable_borrows':[],'mutable_signature':False,'field_arithmetic':[],'oracle_digest_calls':[],'macro_origin':'index_type!(FibreIndex,FIBRE_COUNT), line24; template body SHA; bound=262144'}
# Save index for review; selected inventory uses explicit call resolution below.
(OUT/'NBI1_AST_INDEX.json').write_text(json.dumps({'files':{p:{'sha256':sha(b),'working_copy_matches':Path(p).read_bytes()==b} for p,b in files.items()},'functions':list(funcs.values())},indent=2)+'\n')
print('Indexed',len(files),'source files,',len(funcs),'functions')
# Accepted TX1 branch cuts; hash retains the complete unedited body.
exclude_lines={
 'programs/r1-cost-probe/src/lib.rs':[(26,36),(81,84)],
 'programs/r1-cost-probe/src/r1_pool_adapter.rs':[(944,946),(948,948)],
 'crates/aspis-r1-cost-probe/src/r1_semantic.rs':[],
}
# Latest authoritative leaf packets (older OPEN ledgers are superseded).
leaf_packets={
 ('sampler.rs','','low_base_p_digits'):'leaf-sampler1-20261027/LPk_LEAF.md',
 ('verifier.rs','','echeck'):'leaf-p6-10-20261027/LPl_echeck_LEAF.md',
 ('compact.rs','','check_values'):'leaf-p6-10-20261027/LPl_check_values_LEAF.md',
 ('compact.rs','','expand_values'):'leaf-p6-12-20261027/LPn_expand_values_LEAF.md',
 ('r1_wire.rs','','validate_record_fields'):'leaf-p6-10-20261027/LPl_validate_record_fields_LEAF.md',
 ('r1_wire.rs',"ValidatedRecord<'a>",'decode_k'):'leaf-p6-12-20261027/LPn_decode_k_LEAF.md',
 ('r1_semantic.rs','','claims'):'leaf-p6-12-20261027/LPn_claims_LEAF.md',
 ('fast_pairing.rs','canonical::Dot','push'):'leaf-p6-12-20261027/LPn_Dot_push_LEAF.md',
 ('candidate.rs','','wide_view'):'leaf-p6-13-20261027/LPo_wide_view_LEAF.md',
 ('r1_semantic.rs','','semantic_boundary'):'leaf-p6-13-20261027/LPo_semantic_boundary_LEAF.md',
 ('sampler.rs','','circle_sample'):'leaf-p6-14-20261027/LPp_circle_sample_LEAF.md',
 ('verifier.rs','','checkpoint'):'leaf-p6-11-20261027/LPm_checkpoint_LEAF.md',
 ('verifier.rs','','prepared_claim'):'leaf-p6-18-20261027/LPt_prepared_claim_LEAF.md',
}
for f in funcs.values():
 f['closed_leaf_packet']=leaf_packets.get((Path(f['file']).name,f['owner'],f['name']))
# Normalize paths and type aliases without equating distinct Rust carriers.
alias={'E':'WideExact','K':'QM31','Self':None}
def simpleowner(x):return re.sub(r'<.*','',x).split('::')[-1]
byname={}
for k,f in funcs.items():byname.setdefault(f['name'],[]).append(k)
std=set('len iter iter_mut chunks_exact chunks_exact_mut enumerate zip any all copied rev fold map collect contains is_empty extend_from_slice copy_from_slice fill split_at_mut try_into unwrap ok_or map_err checked_add checked_mul checked_sub checked_div wrapping_add wrapping_sub wrapping_mul rotate_left rotate_right to_vec as_ptr as_mut_ptr as_ref as_mut assume_init cast write resize reserve try_reserve_exact try_reserve swap get_unchecked get_unchecked_mut step_by count into_iter flatten flat_map sum clone copied next first last starts_with split_at to_bytes'.split())
primitives={'u8','u16','u32','u64','u128','i32','usize','Vec','Box','Option','Result','String'}
def resolve(f,c):
 expr=re.sub(r'\s+','',c['expression']);expr=re.sub(r'::<.*>','',expr)
 # Function expressions with arbitrary generic types parsed by suffix here.
 name=re.search(r'([A-Za-z_]\w*)$',expr)
 if not name:return [],'builtin/constructor'
 name=name[1];cand=byname.get(name,[])
 node_info=nodes.get(f['id'])
 if node_info and '.' not in expr and '::' not in expr:
  ni,bi,source=node_info;body_text=source[bi.start_byte:bi.end_byte].decode();sig=source[ni.start_byte:bi.start_byte].decode()
  if re.search(r'\blet\s+'+re.escape(name)+r'\s*=\s*(?:move\s+)?\|',body_text):return [],'inline closure (body inventoried in parent)'
  if re.search(r'\b'+re.escape(name)+r'\s*:\s*fn\b',sig):return [],'function-pointer parameter (caller must bind)'
 if name=='hashv':return [],'Solana SHA256 syscall boundary'
 if name=='digest':
  return [k for k in byname.get('digest',[]) if funcs[k]['file']=='programs/r1-cost-probe/src/lib.rs'],'concrete SolanaDigest backend'
 if name in ('field','powers') and 'aspis-r1-cost-probe' in f['file']:
  return [k for k in cand if funcs[k]['file']=='crates/aspis-r1-cost-probe/src/weights.rs'],'weights import'
 if name in ('circle_sample','qm31_sample') and f['file'].endswith('/r1_wire.rs'):
  return [k for k in cand if funcs[k]['file']=='crates/aspis-r1-cost-probe/src/sampler.rs'],'sampler import'
 if name=='begin' and expr=='wire::begin':
  return [k for k in cand if funcs[k]['file']=='crates/aspis-r1-cost-probe/src/r1_wire.rs'],'wire import'
 if name=='row_shape' and f['file'].endswith('/compact.rs'):
  return [k for k in cand if funcs[k]['file']=='crates/aspis-r1-cost-probe/src/r1_wire.rs'],'wire row_shape import'
 if name=='mul_by_r' and f['file'].endswith('wide_exact.rs'):
  return [k for k in cand if funcs[k]['file']=='crates/aspis-core/src/field.rs'],'field super import'
 if name.startswith('encode_pool_v1_') and 'payment' in name or name in ('encode_pool_v1_private_transfer_public_v1','encode_pool_v1_withdrawal_public_v1'):
  return [k for k in cand if funcs[k]['file'].endswith('payment_relation.rs')],'payment_relation import'
 if name in ('prepare','multiply') and f['file'].endswith('/field.rs') and f['owner']=='PreparedQm31Multiplier':return [],'inline closure (body inventoried in parent)'
 if name in ('Ok','Err','Some','None','Self'):return [],'constructor'
 if expr.startswith(('core::','alloc::','std::')):return [],'standard library'
 if '::' in expr and '.' not in expr.split('::')[0]:
  parts=expr.split('::');qual=parts[-2];qual=alias.get(qual,qual)
  if qual is None:qual=simpleowner(f['owner'])
  if qual in primitives:return [],'standard scalar/container operation'
  if qual in ('Prefix','SemanticTranscript') and 'aspis-r1-cost-probe' in f['file']:
   typed=[k for k in cand if simpleowner(funcs[k]['owner'])==qual and funcs[k]['file']=='crates/aspis-r1-cost-probe/src/r1_wire.rs']
   if typed:return typed,'R1 wire type'
  typed=[k for k in cand if simpleowner(funcs[k]['owner'])==qual]
  if typed:
   own=[k for k in typed if funcs[k]['file']==f['file']]
   if own:typed=own
   elif qual in ('M31','CM31','QM31','WideExact'):typed=[k for k in typed if '/r0/scalar.rs' not in funcs[k]['file']]
   elif qual=='Transcript' and 'aspis-r1-cost-probe' in f['file']:typed=[k for k in typed if 'aspis-r1-cost-probe' in funcs[k]['file']]
   elif qual=='Selectors' and 'pair_forest' in f['file']:typed=[k for k in typed if funcs[k]['file'].endswith('pair_forest_copy_terminal.rs')]
   return typed,'qualified type'
  module=[k for k in cand if Path(funcs[k]['file']).stem==qual or '/'+qual+'/' in funcs[k]['file'] or qual in funcs[k]['owner'].split('::')]
  if parts[0].startswith('aspis_'):module=[k for k in module if '/'+parts[0].replace('_','-')+'/' in funcs[k]['file']]
  if module:return module,'qualified module'
 if '.' in expr:
  receiver=expr.split('.')[0]
  owner=None
  if name=='raw' and f['file'].endswith('fast_pairing.rs'):
   return [k for k in cand if funcs[k]['file']==f['file'] and funcs[k]['owner']=='canonical::Q'],'canonical private-Q receiver'
  if receiver=='self':
   owner=simpleowner(f['owner'])
   if receiver+'.c' in expr and 'fast_pairing' in f['file']:owner='Dot'
  elif receiver in ('t',):owner='Transcript'
  elif receiver in ('transcript','sem'):owner='SemanticTranscript'
  elif receiver=='prefix':owner='Prefix'
  elif receiver in ('pending','weights') and Path(f['file']).name in ('verifier.rs','candidate.rs'):owner='BatchedWeights'
  elif receiver=='geometry':owner='QueryGeometry'
  elif receiver in ('tail','dot'):owner='EbyKDot'
  elif receiver in ('proof_account','public_account','checkpoint_account') and 'owned' in f['file']:owner='OwnedAccount'
  elif receiver in ('public','statement'):
   owner='Public' if receiver=='public' else 'PoolV1PairForestTerminalStatementV1'
  elif receiver in ('record',):owner='ValidatedRecord'
  elif receiver=='selectors':owner='Selectors'
  elif receiver=='scan':owner='QueryScan'
  elif receiver=='u' and f['file'].endswith('fast_domain.rs'):owner='FibreIndex'
  elif receiver=='account' and 'owned' in f['file']:owner='OwnedAccount'
  if owner:
   if owner in ('Prefix','SemanticTranscript','ValidatedRecord') and 'aspis-r1-cost-probe' in f['file']:
    typed=[k for k in cand if simpleowner(funcs[k]['owner'])==owner and funcs[k]['file']=='crates/aspis-r1-cost-probe/src/r1_wire.rs']
    if typed:return typed,'R1 wire receiver'
   if owner=='Public' and 'aspis-r1-cost-probe' in f['file']:
    typed=[k for k in cand if simpleowner(funcs[k]['owner'])==owner and funcs[k]['file'].endswith('pair_forest_semantic_terminal.rs')]
    if typed:return typed,'R1 semantic public receiver'
   typed=[k for k in cand if simpleowner(funcs[k]['owner'])==owner]
   if typed:
    own=[k for k in typed if funcs[k]['file']==f['file']]
    if own:typed=own
    elif owner=='Transcript' and 'aspis-r1-cost-probe' in f['file']:typed=[k for k in typed if 'aspis-r1-cost-probe' in funcs[k]['file']]
    elif owner=='Selectors' and 'pair_forest' in f['file']:typed=[k for k in typed if funcs[k]['file'].endswith('pair_forest_copy_terminal.rs')]
    return typed,'receiver owner'
  if name in std or name in ('push','hash','trace','get'):return [],'standard library/runtime or callback'
  # Field operation overloads: record carrier candidates, do not choose one silently.
  if name in ('mul','add','sub','square','inv','double','neg','pow','half','mul_m31','mul_qm31','c0','c1','to_le_bytes','to_limbs','from_qm31','write_le_bytes'):
   if f['file'].endswith('/field.rs') or '/field/' in f['file']:
    own=[k for k in cand if funcs[k]['file']==f['file'] and funcs[k]['owner']==f['owner']]
    if own:return own,'same field owner'
   typed=[k for k in cand if (funcs[k]['file'].endswith('/field.rs') or '/field/' in funcs[k]['file']) and simpleowner(funcs[k]['owner']) in ('M31','CM31','QM31','WideExact')]
   return typed,'field-carrier overapproximation'
 else:
  local=[k for k in cand if funcs[k]['file']==f['file'] and (not funcs[k]['owner'] or funcs[k]['owner']==f['owner'])]
  if local:
   free=[k for k in local if not funcs[k]['owner']]
   return free or local,'lexical function'
  nested=[k for k in cand if funcs[k]['file']==f['file'] and funcs[k]['owner']==f['owner']+'::'+f['name']]
  if nested:return nested,'nested function'
  if f['owner']:
   sibling=[k for k in cand if funcs[k]['file']==f['file'] and funcs[k]['owner']==f['owner']]
   if sibling:return sibling,'nested sibling function'
  # candidate is a child of verifier and inherits super::*.
  if f['file'].endswith('/candidate.rs'):
   local=[k for k in cand if funcs[k]['file'].endswith('aspis-r1-cost-probe/src/verifier.rs') and not funcs[k]['owner']]
   if local:return local,'super import'
 if name in ('trace',):return [],'inline callback'
 if len(cand)==1:return cand,'unique source symbol'
 return [],'unresolved project call' if cand else 'external/constructor/callback'
# Function pointer calls and a few receiver facts that are not CallExpressions.
extra={('verifier.rs','BatchedWeights','value'):[('field.rs','M31','reduce_u64')],('r1_semantic.rs','','semantic_boundary'):[('field.rs','QM31','add')]}
roots=[k for k,f in funcs.items() if f['file']=='programs/r1-cost-probe/src/lib.rs' and f['name']=='process_r1_cost_probe_instruction']
selected=set();pending=list(roots);unresolved=[]
# Explicit exclusion of non-TX1 branches and cfg-only alternative bodies.
excluded_names={'stage2','stage2_owned','tx2','tx2_authenticated','tx2_common','resume','lifecycle_init','lifecycle_write','lifecycle_finalize','authenticate_asq8_accounts','validate_asq8','emit_result','compact_values','compact_semantic'}
while pending:
 k=pending.pop()
 if k in selected:continue
 selected.add(k);f=funcs[k];edges=[]
 for c in f['calls']:
  if any(lo<=c['line']<=hi for lo,hi in exclude_lines.get(f['file'],[])):continue
  targets,how=resolve(f,c)
  targets=[t for t in targets if funcs[t]['name'] not in excluded_names]
  edge={**c,'targets':targets,'resolution':how}
  edges.append(edge)
  if not f['closed_leaf_packet']:pending.extend(targets)
 for bn,owner,name in extra.get((Path(f['file']).name,f['owner'],f['name']),[]):
  ts=[t for t,g in funcs.items() if Path(g['file']).name==bn and g['owner']==owner and g['name']==name];edges.append({'expression':owner+'::'+name,'line':f['line'],'targets':ts,'resolution':'function value'});pending.extend(ts)
 f['callees']=edges
 if len(selected)>1400:raise RuntimeError('call resolution overgrowth requires split')
(OUT/'NBI1_REACH_DRAFT.json').write_text(json.dumps({'roots':roots,'functions':[funcs[k] for k in sorted(selected)]},indent=2)+'\n')
print('Selected',len(selected),'functions')
print('Unresolved project calls:')
for k in sorted(selected):
 f=funcs[k]
 if f['closed_leaf_packet']:continue
 for e in f['callees']:
  if e['resolution']=='unresolved project call':print(k,e['expression'])
