"""Frozen Pool source AST plus emitted MIR census, retaining unresolved sites."""
from pathlib import Path
import sys,subprocess,json,re,hashlib,lzma,collections
sys.dont_write_bytecode=True
sys.path.insert(0,'/private/tmp/NFZ-parser-20261104')
from tree_sitter import Language,Parser
import tree_sitter_rust
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
parser=Parser(Language(tree_sitter_rust.language()))
sha=lambda b:hashlib.sha256(b).hexdigest()
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def ancestors(n):
 while n.parent:n=n.parent;yield n
def text(n,b):return b[n.start_byte:n.end_byte].decode() if n else ''
def category(s):
 if re.search(r'(?:try_)?borrow(?:_mut)?(?:_data|_lamports)?$',s):return 'exclusive' if ('mut' in s) else 'shared'
 if s in ['data_is_empty','data_len','lamports']:return 'accessor'
 if s in ['invoke','invoke_signed','invoke_unchecked','invoke_signed_unchecked']:return 'cpi'
 return None
listing=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'programs/aspis-pool/src'],cwd=R,text=True).splitlines()
functions=[];sources={};pins=[]
for p in listing:
 if not p.endswith('.rs'):continue
 b=subprocess.check_output(['git','show',F+':'+p],cwd=R);sources[p]=b.decode();pins.append(dict(path=p,sha256=sha(b),bytes=len(b)))
 root=parser.parse(b).root_node;assert not root.has_error,p
 for n in walk(root):
  if n.type!='function_item' or n.child_by_field_name('body') is None:continue
  body=n.child_by_field_name('body');parents=list(ancestors(n));scopes=[]
  for a in reversed(parents):
   if a.type in ['mod_item','function_item']:scopes.append(text(a.child_by_field_name('name'),b))
   if a.type=='impl_item':scopes.append(text(a.child_by_field_name('type'),b))
  name=text(n.child_by_field_name('name'),b);key=p+'::'+'::'.join(scopes+[name]);calls=[];owners=[]
  for c in walk(body):
   if any(a.type=='function_item' and a!=n for a in ancestors(c) if a.start_byte>=body.start_byte):continue
   if c.type=='field_expression' and text(c.child_by_field_name('field'),b)=='owner':owners.append(c.start_point.row+1)
   if c.type!='call_expression':continue
   fn=c.child_by_field_name('function');raw=text(fn,b);short=raw.rsplit('.',1)[-1].rsplit('::',1)[-1];cat=category(short)
   item=dict(line=c.start_point.row+1,end=c.end_point.row+1,expression=raw,callee=short,category=cat,byte_range=[c.start_byte,c.end_byte],arguments=text(c.child_by_field_name('arguments'),b))
   if cat in ['exclusive','shared']:
    scope=next((a for a in ancestors(c) if a.type=='block'),body)
    stmt=next((a for a in ancestors(c) if a.type in ['let_declaration','expression_statement']),None)
    item['lexical_block']=[scope.start_point.row+1,scope.end_point.row+1]
    item['statement_end']=stmt.end_point.row+1 if stmt else None
    item['statement']=text(stmt,b)
    if stmt and stmt.type=='let_declaration':
     item['binding']=text(stmt.child_by_field_name('pattern'),b)
     item['initializer']=text(stmt.child_by_field_name('value'),b)
    item['scope_status']='lexical candidate only; MIR drops and carrier use require review'
   if short=='drop':item['arguments']=text(c.child_by_field_name('arguments'),b)
   calls.append(item)
  cfg=[]
  for owner in [n]+parents:
   prev=owner.prev_named_sibling
   while prev and prev.type=='attribute_item':cfg.append(text(prev,b));prev=prev.prev_named_sibling
  impl=next((a for a in parents if a.type=='impl_item'),None)
  functions.append(dict(function=key,path=p,name=name,start=n.start_point.row+1,end=n.end_point.row+1,impl_start=impl.start_point.row+1 if impl else None,scope=scopes,cfg=cfg,body_sha256=sha(b[body.start_byte:body.end_byte]),calls=calls,owner_checks=sorted(set(owners)),mir_headers=[],mir_events=[]))
byname=collections.defaultdict(list)
for f in functions:byname[f['name']].append(f)
mir=E/'NIK_M001_artifacts/NIK_pool.mir.xz';events=[];headers=[];unknown=[];all_calls=[]
if mir.exists():
 raw=lzma.decompress(mir.read_bytes());lines=raw.decode().splitlines();owner=None;header='';localtypes={}
 for i,line in enumerate(lines,1):
  if line.startswith('fn '):
   header=line;h=line[3:].split('(')[0];name=h.split('::')[-1].split('<')[0];candidates=byname[name]
   m=re.search(r'<impl at ([^:]+):(\d+):',line);closure=re.search(r'closure@([^:]+):(\d+):',line)
   if closure:candidates=[f for f in functions if f['path']==closure[1] and f['start']<=int(closure[2])<=f['end']]
   elif m:candidates=[f for f in candidates if f['path']==m[1] and f['impl_start']==int(m[2])]
   else:
    exact=[f for f in candidates if (Path(f['path']).stem+'::'+'::'.join(f['scope']+[name]))==h or ('::'.join(f['scope']+[name])==h and f['path'].endswith('/lib.rs'))]
    if exact:candidates=exact
   owner=candidates[0] if len(candidates)==1 else None;localtypes={}
   if owner:owner['mir_headers'].append(dict(line=i,header=header))
   headers.append(dict(line=i,header=header,source=owner['function'] if owner else None))
  m=re.search(r'let(?: mut)? (_\d+): (.*);',line)
  if m:localtypes[m[1]]=m[2]
  if ' -> [' not in line:continue
  if ' = ' in line:
   rhs=line.split(' = ',1)[1].split(' -> [',1)[0]
   all_calls.append(dict(mir_line=i,caller=owner['function'] if owner else None,header=header,expression=rhs))
  cats=[]
  for target in ['try_borrow_mut_data','try_borrow_mut_lamports','try_borrow_data','try_borrow_lamports','data_is_empty','data_len','lamports','try_borrow_mut','try_borrow','borrow_mut','borrow','invoke_signed_unchecked','invoke_unchecked','invoke_signed','invoke']:
   if re.search(r'(?<!\w)'+target+r'(?:>|::|\()',line):cats.append(target)
  drop=re.search(r'drop\((_\d+)\)',line)
  drop_type=localtypes.get(drop[1],'') if drop else ''
  if not cats and not ('RefMut<' in drop_type or 'Ref<' in drop_type):continue
  e=dict(mir_line=i,caller=owner['function'] if owner else None,header=header,targets=cats,kind='drop' if drop else 'call',guard_type=drop_type,mir=line.strip())
  if owner:
   e['source_candidates']=[dict(line=c['line'],expression=c['expression']) for c in owner['calls'] if c['callee'] in cats]
   e['source_check']='AGREES' if e['source_candidates'] or drop else 'UNRESOLVED'
   owner['mir_events'].append(e)
  else:e['source_check']='UNRESOLVED';unknown.append(e)
  events.append(e)
 source_edges=[]
 # Preserve all potential source edges; MIR-only graph is not replaced by names.
 for f in functions:
  if not f['mir_headers']:continue
  for c in f['calls']:
   targets=[g['function'] for g in byname.get(c['callee'],[]) if g['mir_headers']]
   if targets:source_edges.append(dict(caller=f['function'],line=c['line'],expression=c['expression'],candidates=targets,status='AST candidate; resolve receiver/module and MIR before composition'))
else:raw=b'';source_edges=[]
out=dict(frozen_revision=F,parser={'tree-sitter':'0.25.2','tree-sitter-rust':'0.24.2'},source_pins=pins,source_authority='git frozen revision; AST includes nondeployed/test functions labelled by absence of MIR',mir_sha256=sha(raw) if raw else None,mir_headers=headers,mir_calls=all_calls,events=events,functions=functions,source_edges=source_edges,unknown=unknown,counts=dict(source_functions=len(functions),mir_functions=len(headers),source_with_mir=sum(bool(f['mir_headers']) for f in functions),events=len(events),unresolved=sum(e['source_check']!='AGREES' for e in events)))
(E/'NIK_CENSUS.json').write_text(json.dumps(out,indent=1)+'\n')
print('NIK census '+json.dumps(out['counts'],separators=(',',':')))
