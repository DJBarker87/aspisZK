"""Whole-inventory source AST discovery. Deliberately NOT compiler authority.

All candidates remain unreviewed until pinned deployed compiler evidence exists.
Anonymous closures are owned by their enclosing caller, as in NBI2.
"""
import sys,pathlib,json,lzma,hashlib,re,collections,subprocess
sys.dont_write_bytecode=True
sys.path.insert(0,'/private/tmp/NFZ-parser-20261104')
from tree_sitter import Language,Parser
import tree_sitter_rust
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files=json.loads(lzma.decompress((E/'NFZ_FROZEN_SOURCE.json.xz').read_bytes()))
L=json.loads(lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read());rows=L['rows'];by=collections.defaultdict(list);graph=collections.defaultdict(set)
for r in rows:by[r['function']].append(r['row']);graph[r['function']].update(r['canonical_callees'])
parser=Parser(Language(tree_sitter_rust.language()));decls={};trees={};impls=[]
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def txt(n,b):return b[n.start_byte:n.end_byte].decode() if n else ''
def parents(n):
 while n.parent:n=n.parent;yield n
for path,s in sorted(files.items()):
 if not path.endswith('.rs'):continue
 b=s.encode();t=parser.parse(b);trees[path]=(b,t)
 for n in walk(t.root_node):
  if n.type=='impl_item' and txt(n.child_by_field_name('trait'),b).endswith('CodeField'):
   impls.append(dict(file=path,line=n.start_point.row+1,type=txt(n.child_by_field_name('type'),b),trait=txt(n.child_by_field_name('trait'),b)))
  if n.type!='function_item':continue
  scopes=[];trait=None
  for p in reversed(list(parents(n))):
   if p.type in ['mod_item','function_item']:scopes.append(txt(p.child_by_field_name('name'),b))
   if p.type=='impl_item':scopes.append(txt(p.child_by_field_name('type'),b));trait=txt(p.child_by_field_name('trait'),b)
  name=txt(n.child_by_field_name('name'),b);body=n.child_by_field_name('body')
  if body is None:continue
  key=path+'::'+'::'.join(scopes+[name])
  item=dict(function=key,file=path,line=n.start_point.row+1,body_range=[body.start_byte,body.end_byte],trait=trait,name=name,body_sha256=hashlib.sha256(b[body.start_byte:body.end_byte]).hexdigest())
  decls.setdefault(key,[]).append((item,body))

def attrs(n,b):
 out=[]
 for x in [n,*parents(n)]:
  p=x.prev_named_sibling
  while p and p.type in ['attribute_item','line_comment','block_comment']:
   if p.type=='attribute_item':out.append(txt(p,b))
   p=p.prev_named_sibling
 return sorted(set(out))

def resolve(spelling,file):
 # Discovery only; ambiguous overloads are returned, never chosen silently.
 spelling=re.sub(r'::<[^>]*>','',spelling).strip();tail=spelling.split('::')[-1]
 if spelling.startswith('<') and 'as CodeField>' in spelling:
  owner=spelling[1:].split(' as ')[0];key='crates/aspis-core/src/r0/scalar.rs::'+owner+'::'+tail
  return [key] if key in decls else []
 if spelling=='E::from_m31' and ('WideExact as E' in files[file] or 'field::WideExact as E' in files[file]):return ['crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31']
 if spelling.startswith(('Self::','E::','K::','F::')):return []
 if spelling in ['CM31::from_m31','QM31::from_cm31','WideExact::from_qm31']:
  owner=spelling.split('::')[0];p='crates/aspis-core/src/field/wide_exact.rs' if owner=='WideExact' else 'crates/aspis-core/src/field.rs'
  return [p+'::'+spelling]
 if spelling.split('::')[0] in ['u8','u16','u32','u64','u128','usize','i8','i16','i32','i64','i128','isize','bool','core','std','alloc']:return []
 candidates=[k for k in decls if k.split('::')[-1]==tail]
 local=[k for k in candidates if k.split('::')[0]==file and (len(spelling.split('::'))==1 or k.endswith('::'+spelling))]
 if local:return sorted(local)
 if spelling.startswith('crate::'):
  prefix=file.split('/src/')[0]+'/src/';suffix=spelling[len('crate::'):]
 elif spelling.startswith(('aspis_core::','aspis_statement::','aspis_r1_cost_probe::')):
  prefix='crates/'+spelling.split('::')[0].replace('_','-')+'/src/';suffix=spelling.split('::',1)[1]
 else:return []
 matches=[]
 for k in candidates:
  source,owner=k.split('::',1)
  if source.startswith(prefix):
   mod=source[len(prefix):].removesuffix('.rs').removesuffix('/mod')
   qualified=(mod.replace('/','::')+'::'+owner) if mod not in ['lib','mod'] else owner
   if qualified==suffix:matches.append(k)
 return sorted(matches)


root='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction'
seen={root};q=collections.deque([root])
while q:
 for t in graph[q.popleft()]:
  if t not in seen:seen.add(t);q.append(t)
sites=[];candidates=[];all_from=[]
combinators={'map','map_err','and_then','or_else','unwrap_or_else','filter','filter_map','flat_map','find_map','for_each','fold','try_fold','any','all','position','rposition','find','sort_by','sort_unstable_by','sort_by_key','sort_unstable_by_key','from_fn','map_or','map_or_else','inspect','inspect_err','retain','retain_mut','is_some_and','is_ok_and','ok_or_else','then','then_some','reduce','try_for_each','zip','chain','cloned','copied','enumerate','collect','extend'}
trait_methods={'from_m31','add','sub','neg','mul','try_inv'}
# Scan ALL inventory bodies, including rows with no entry path; source contexts
# carry cfg attributes and remain pending compiler classification.
for f,rr in sorted(by.items()):
 row=next(r for r in rows if r['function']==f);path=row['source_file'];b,t=trees[path]
 matches=[(item,n) for item,n in decls.get(f,[]) if item['body_range']==row['frozen_body_byte_range']]
 if not matches:
  # NBI macro-origin FibreIndex methods: their token template has no AST call.
  sites.append(dict(caller=f,rows=rr,category='macro-template',status='requires compiler macro expansion',source_range=row['frozen_body_byte_range']));continue
 item,body=matches[0];assert item['body_sha256']==row['frozen_body_sha256']
 for n in walk(body):
  if n.type!='call_expression':continue
  fn=n.child_by_field_name('function');args=n.child_by_field_name('arguments');spelling=txt(fn,b)
  if fn.type=='generic_function':fn=fn.child_by_field_name('function');spelling=txt(fn,b)
  name=txt(fn.child_by_field_name('field'),b) if fn.type=='field_expression' else spelling.split('::')[-1]
  is_trait=('as CodeField>' in spelling or (name in trait_methods and spelling.startswith(('E::','F::','K::','WideExact::','CodeField::'))))
  if name=='from_m31':all_from.append(dict(caller=f,rows=rr,line=n.start_point.row+1,syntax=spelling,attributes=attrs(n,b),targets=resolve(spelling,path),entry_union_member=f in seen))
  if is_trait:
   target=resolve(spelling,path)
   site=dict(caller=f,rows=rr,kind='trait-dispatch',line=n.start_point.row+1,syntax=spelling,targets=target,attributes=attrs(n,b));sites.append(site)
   for dest in target or [None]:
    if dest not in graph[f]:candidates.append(dict(**site,to=dest,covered_by_existing_row=dest in by,existing_rows=by.get(dest,[]),caller_entry_union_member=f in seen,reachability='UNRESOLVED_REQUIRES_MIR',resolution='source-discovered; not compiler-reviewed'))
  if name not in combinators:continue
  for arg in args.named_children if args else []:
   # Non-closure arguments can be data; keep those unresolved rather than
   # claiming every iterator argument is a function pointer.
   if arg.type=='closure_expression':
    refs=[]
    for c in walk(arg):
     if c.type=='call_expression':
      ff=c.child_by_field_name('function')
      if ff.type in ['identifier','scoped_identifier','generic_function']:refs.append((txt(ff,b),c.start_point.row+1))
    kind='inline-closure';names=refs
   elif arg.type in ['identifier','scoped_identifier','generic_function']:
    kind='named-callback-or-data';names=[(txt(arg,b),arg.start_point.row+1)]
   else:continue
   site=dict(caller=f,rows=rr,kind='callback',adapter=name,line=n.start_point.row+1,argument=txt(arg,b),argument_kind=kind,attributes=attrs(n,b));sites.append(site)
   for raw,line in names:
    target=resolve(raw,path)
    # A bare local variable which does not name any function is not an
    # invented function edge. Preserve the unresolved site in the scan.
    if not target:continue
    for dest in target:
     if dest not in graph[f]:candidates.append(dict(**site,to=dest,reference=raw,reference_line=line,covered_by_existing_row=dest in by,existing_rows=by.get(dest,[]),caller_entry_union_member=f in seen,reachability='UNRESOLVED_REQUIRES_MIR',resolution='source candidates; overload/cfg/callback-vs-data needs MIR'))
# Also inspect every CodeField implementation's embedding chain, including
# declarations absent from the canonical inventory. This avoids hiding new rows.
chains=[]
for f,ds in sorted(decls.items()):
 for item,body in ds:
  if item['trait']=='CodeField' and item['name']=='from_m31':
   b,_=trees[item['file']]
   calls=[]
   for n in walk(body):
    if n.type=='call_expression':
     raw=txt(n.child_by_field_name('function'),b);targets=resolve(raw.replace('Self::',f.split('::')[-2]+'::'),item['file'])
     calls.append(dict(line=n.start_point.row+1,syntax=raw,targets=targets))
     for dest in targets:
      if dest not in graph[f]:candidates.append(dict(caller=f,rows=by.get(f,[]),kind='trait-dispatch' if 'as CodeField>' in raw else 'trait-implementation-child',line=n.start_point.row+1,syntax=raw,to=dest,covered_by_existing_row=dest in by,existing_rows=by.get(dest,[]),caller_entry_union_member=f in seen,reachability='UNRESOLVED_REQUIRES_MIR',resolution='new source-only dependency candidate'))
   chains.append(dict(**item,rows=by.get(f,[]),calls=calls))
for i,c in enumerate(candidates,1):c['id']=f'NFZ_C{i:04}';c['evidence']=dict(path=c['caller'].split('::')[0],revision=FROZEN,line=c['line']);c['admitted']=False
out=dict(schema_version=1,frozen_revision=FROZEN,authority='source AST DISCOVERY ONLY, not MIR',complete=False,reason='one allowed scope stopped before compilation; no compiler resolution claim',counts=dict(inventory_rows=len(rows),inventory_functions=len(by),source_functions=len(decls),sites=len(sites),candidate_edges=len(candidates),new_function_candidates=len({c['to'] for c in candidates if c['to'] and not c['covered_by_existing_row']})),candidates=candidates)
def put(n,d):(E/n).write_text(json.dumps(d,indent=1)+'\n')
put('NFZ_CANDIDATES.json',out);put('NFZ_SCAN.json',dict(parser={'tree-sitter':'0.25.2','tree-sitter-rust':'0.24.2'},scope='all unique inventory function bodies, plus all CodeField impl embeddings in the frozen source payload',sites=sites,CodeField_impls=impls,CodeField_embedding_chain=chains,from_m31_calls=all_from,new_function_candidates=sorted({c['to'] for c in candidates if c['to'] and not c['covered_by_existing_row']})))
print(json.dumps(out['counts']));print('from_m31 sites',len(all_from),'impls',impls)
