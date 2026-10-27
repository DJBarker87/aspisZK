#!/usr/bin/env python3
"""Source-only inventory. Requires tree-sitter{,-rust}; never invokes Rust/Lean/Kani.
Bodies include braces, verbatim frozen bytes. Calls include nested closures.
Manual dispatch/feature/type resolutions are recorded separately, never guessed silently.
"""
import sys, subprocess, json, hashlib, pathlib, re, collections
sys.path.insert(0, '/private/tmp/NBI2-parser')
from tree_sitter import Language, Parser
import tree_sitter_rust
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=pathlib.Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
parser=Parser(Language(tree_sitter_rust.language()))
# Validated parser versions: tree-sitter==0.25.2, tree-sitter-rust==0.24.2.
# 0.26.0 bus-faulted during source inspection; no proof or Rust process ran.
def sha(b): return hashlib.sha256(b).hexdigest()
def walk(n):
 yield n
 for c in n.named_children: yield from walk(c)
def txt(n,b): return b[n.start_byte:n.end_byte].decode() if n else ''
def frozen():
 rows=subprocess.check_output(['git','ls-tree','-rz',REV,'--','crates/','programs/'],cwd=ROOT).split(b'\0')
 rows=[r.split(b'\t',1) for r in rows if r and r.endswith(b'.rs') and b'/src/' in r]
 p=subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for meta,path in rows:
  oid=meta.split()[-1];p.stdin.write(oid+b'\n');p.stdin.flush();hdr=p.stdout.readline();sz=int(hdr.split()[-1]);b=p.stdout.read(sz);p.stdout.read(1)
  yield path.decode(),b
 p.stdin.close();p.wait()
def call_attrs(n,b):
 attrs=[]
 while n and n.type!='function_item':
  prev=n.prev_named_sibling
  while prev and prev.type in ('attribute_item','line_comment','block_comment'):
   if prev.type=='attribute_item':attrs.append(txt(prev,b))
   prev=prev.prev_named_sibling
  n=n.parent
 return attrs
def collect():
 funcs={}; files={}
 for path,b in frozen():
  files[path]=sha(b);tree=parser.parse(b)
  if tree.root_node.has_error: print("parse warnings",path,flush=True)
  for n in walk(tree.root_node):
   if n.type!='function_item': continue
   parents=[];p=n.parent
   while p:
    parents.append(p);p=p.parent
   scopes=[]
   for p in reversed(parents):
    if p.type=='function_item':scopes.append(txt(p.child_by_field_name('name'),b))
    if p.type=='mod_item':scopes.append(txt(p.child_by_field_name('name'),b))
    if p.type=='impl_item':scopes.append(txt(p.child_by_field_name('type'),b))
   name=txt(n.child_by_field_name('name'),b);q='::'.join(scopes+[name]);key=path+'::'+q
   body=n.child_by_field_name('body');bodyb=b[body.start_byte:body.end_byte]
   # Preserve feature/test context for review, including enclosing module attributes.
   attrs=[]
   for node in [n]+parents:
    prev=node.prev_named_sibling
    while prev and prev.type in ('attribute_item','line_comment','block_comment'):
     if prev.type=='attribute_item':attrs.append(txt(prev,b))
     prev=prev.prev_named_sibling
   calls=[]
   for c in walk(body):
    if c.type=='call_expression':
     f=c.child_by_field_name('function');raw=txt(f,b)
     if f.type=='generic_function':f=f.child_by_field_name('function');raw=txt(f,b)
     if f.type=='field_expression':
      method=txt(f.child_by_field_name('field'),b);receiver=txt(f.child_by_field_name('value'),b)
      calls.append({'syntax':raw,'name':method,'receiver':receiver,'line':c.start_point.row+1,'cfg':call_attrs(c,b)})
     else:calls.append({'syntax':raw,'name':raw.split('::')[-1],'line':c.start_point.row+1,'cfg':call_attrs(c,b)})
   funcs[key]={'id':key,'file':path,'name':q,'short_name':name,'line':n.start_point.row+1,'end_line':n.end_point.row+1,'body_start_byte':body.start_byte,'body_end_byte':body.end_byte,'body_sha256':sha(bodyb),'file_sha256':sha(b),'attributes':attrs,'local_closures':[txt(c.child_by_field_name('pattern'),b) for c in walk(body) if c.type=='let_declaration' and c.child_by_field_name('value') and c.child_by_field_name('value').type=='closure_expression'],'calls':calls,'loops':[{'line':c.start_point.row+1,'kind':c.type} for c in walk(body) if c.type in ('for_expression','while_expression','loop_expression')], 'iterator_loops':[{'line':c['line'],'syntax':c['syntax']} for c in calls if c['name'] in ['fold','for_each','any','all','map','from_fn','collect','contains','position']], 'mutable_borrows':{'signature': '&mut' in txt(n,b)[:body.start_byte-n.start_byte], 'body':bool(re.search(rb'&\s*mut\b|try_borrow_mut',bodyb))},'field_calls':[c for c in calls if c['name'] in ['mul','mul_m31','mul_qm31','inv','pow','square','add','sub','half','double','reduce','reduce_u64','push','finish']], 'effect_calls':[c for c in calls if c['name'] in ['digest','hashv','hash','create_program_address','find_program_address','set_return_data','get','try_borrow_data','try_borrow_mut_data']], '_body':bodyb.decode()}
 # index_type! emits real methods whose templates are opaque token trees to the parser.
 path='crates/aspis-core/src/r0/domain.rs'
 b=subprocess.check_output(['git','show',REV+':'+path],cwd=ROOT)
 for name in ('new','get'):
  m=re.search(rb'pub (?:const )?fn '+name.encode()+rb'\(',b);start=b.index(b'{',m.start());depth=1;end=start+1
  while depth:
   depth+=(b[end]==123)-(b[end]==125);end+=1
  key=path+'::FibreIndex::'+name
  funcs[key]={'id':key,'file':path,'name':'FibreIndex::'+name,'short_name':name,'line':b[:m.start()].count(b'\n')+1,'end_line':b[:end].count(b'\n')+1,'body_start_byte':start,'body_end_byte':end,'body_sha256':sha(b[start:end]),'file_sha256':sha(b),'attributes':[],'calls':[],'loops':[],'iterator_loops':[],'mutable_borrows':{'signature':False,'body':False},'field_calls':[],'effect_calls':[],'macro_origin':'index_type!(FibreIndex, FIBRE_COUNT) at domain.rs:24; body SHA hashes the verbatim method template, substituting bound=262144','_body':b[start:end].decode()}
 return funcs,files
if __name__=='__main__':
 funcs,files=collect()
 data={'revision':REV,'file_count':len(files),'functions':funcs,'files':files}
 (OUT/'NBI2_scan.json').write_text(json.dumps(data,indent=2)+'\n')
 print('parsed',len(files),'files;',len(funcs),'functions')
