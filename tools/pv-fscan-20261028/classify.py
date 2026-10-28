"""Source-first classification. Ambiguous/macro/cfg mappings never earn A."""
from pathlib import Path
import json,lzma,re,hashlib,sys,difflib,collections
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
P=Parser(Language(tree_sitter_rust.language()));E=Path('evidence/pv-fscan-20261028');O=E/'classification'
src=json.loads(lzma.open(O/'sources.json.xz').read()); scan=json.loads((E/'scan.json').read_text()); rows=[r for r in scan['rows'] if r['status']=='SUSPENDED']; reached={r['id']:r for r in json.loads(lzma.open(E/'reached-audit.json.xz').read())}
sha=lambda b:hashlib.sha256(b).hexdigest()
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def txt(n,b):return b[n.start_byte:n.end_byte].decode() if n else ''
def toks(s):return re.findall(r'\w+|[^\s]',s)
index=collections.defaultdict(list)
for key,v in src['files'].items():
 b=v['text'].encode();tree=P.parse(b)
 for n in walk(tree.root_node):
  if n.type!='function_item':continue
  body=n.child_by_field_name('body'); name=txt(n.child_by_field_name('name'),b)
  if not body:continue
  par=n.parent;impl='';cfg=[]
  while par:
   if par.type=='impl_item':impl=txt(par,b).split('{',1)[0]
   par=par.parent
  # Complete function item, including its signature; leading attributes are retained separately.
  attrs=[];prev=n.prev_named_sibling
  while prev and prev.type in ['attribute_item','line_comment','block_comment']:
   if prev.type=='attribute_item':attrs.append(txt(prev,b))
   prev=prev.prev_named_sibling
  rec=dict(key=key,line=n.start_point.row+1,end_line=n.end_point.row+1,impl=impl,name=name,body=txt(body,b),item=txt(n,b),attrs=attrs,file_sha256=v['sha256'],body_sha256=sha(b[body.start_byte:body.end_byte]),item_sha256=sha(b[n.start_byte:n.end_byte]))
  index[(key.split('/')[0],name)].append(rec)
# Project source uses the scan's frozen mirror identity record; no claim about historical harness identity.
pins=json.loads((E/'runtime-source-pins.json').read_text());pinmap={x['path']:x for x in pins['files']}
def locate(f,c):
 method=f.split('(_',1)[0].split('()',1)[0].split('::')[-1];method=method.split('{closure')[0] if '{closure' in method else method
 path=re.search(r'(library/[^:]+\.rs|registry/[^:]+\.rs|crates/[^:]+\.rs)',f)
 closure=re.search(r'\{closure@([^:]+):(\d+):',f)
 if closure:
  # The line belongs to one MIR cohort. Resolve by enclosing function name, never reuse that line on the other cohort.
  outer=f.split('::{closure#',1)[0].split('::')[-1]
  pathstr=re.sub(r'registry/([^/]+)-\d[^/]*/',r'registry/\1/',closure[1])
  cand=[v for v in index[(c,outer)] if v['key']==c+'/'+pathstr]
 else:
  cand=index[(c,method)]
  if path:
   pathstr=re.sub(r'registry/([^/]+)-\d[^/]*/',r'registry/\1/',path[1]);cand=[v for v in cand if v['key']==c+'/'+pathstr]
  else:
   if f.startswith('core::take('):
    return [v for v in cand if v['key']==c+'/library/core/src/mem/mod.rs' and not v['impl']]
   owner=f.split('::')[0];cand=[v for v in cand if (('/library/'+owner+'/') in '/'+v['key']) or (('/registry/'+owner.replace('_','-')+'/') in '/'+v['key'])]
 if len(cand)>1 and not path and not closure:
  # Free source namespace is useful only when it names an actual unique file.
  ns=f.split('::')[1:-1]; prefix=c+'/library/'+f.split('::')[0]+'/src/'
  paths=[prefix+'/'.join(ns)+'.rs',prefix+'/'.join(ns)+'/mod.rs']
  direct=[v for v in cand if v['key'] in paths and not v['impl']]
  if direct:cand=direct
 if len(cand)>1:
  imp=re.search(r'::impl(.+?)>::',f)
  if imp:
   exact=[v for v in cand if toks('impl'+imp[1])==toks(v['impl'])]
   if exact:cand=exact
 return cand
functions={};allfs=sorted({f for r in rows for vs in reached[r['id']].get('reached_functions',{}).values() for f in vs}|{f['function'] for r in rows for f in r['matched_changed_bodies']})
for f in allfs:
 rec={'function':f,'class':'D'}
 if f.startswith('aspis_'):
  pm=re.search(r'(crates/[^:]+\.rs)',f)
  if pm and pm[1] in pinmap:
   pin=pinmap[pm[1]];rec.update(source_file=pin,reason='same frozen project file; per-function cfg selection and historical source association not certified',source_identity='file-level only')
  else:rec['reason']='project function source span/cfg association unresolved'
 else:
  aa=locate(f,'evidence');bb=locate(f,'deployed')
  rec['candidates']={c:[{k:v[k] for k in ['key','line','end_line','impl','name','file_sha256','body_sha256','item_sha256','attrs']} for v in vs] for c,vs in [('evidence',aa),('deployed',bb)]}
  if len(aa)==len(bb)==1:
   a,b=aa[0],bb[0];rec['source_evidence']={c:{k:v[k] for k in ['key','line','end_line','file_sha256','body_sha256','item_sha256','attrs']} for c,v in [('evidence',a),('deployed',b)]}
   rec['body_bytes_identical']=a['body']==b['body'];rec['item_bytes_identical']=a['item']==b['item'];rec['impl_identical']=a['impl']==b['impl']
   rawdiff=a['item']!=b['item'] or a['impl']!=b['impl']
   cfg=any('cfg' in x for x in a['attrs']+b['attrs']) or '#[cfg' in a['item']+b['item'] or 'cfg!' in a['item']+b['item']
   if rawdiff:
    rec['class']='B' if f.startswith(('core::','alloc::','std::')) else 'C';rec['reason']='actual source item or enclosing impl differs; see diff (before cfg evaluation)'
    rec['diff']=''.join(difflib.unified_diff((a['impl']+'\n'+a['item']).splitlines(True),(b['impl']+'\n'+b['item']).splitlines(True),fromfile=a['key'],tofile=b['key']))
   elif cfg:rec['reason']='raw source identical, cfg attributes/macro selection needs resolution'
   else:rec.update(source_identity='complete raw function item and enclosing impl byte-identical',reason='source identical; compiler/profile lowering candidate',class_hint='A-function',**{'class':'A-function'})
  else:rec['reason']='source symbol or macro expansion not uniquely mapped'
 functions[f]=rec
result=[]
for r in rows:
 fs=sorted(set(f for vs in reached[r['id']].get('reached_functions',{}).values() for f in vs)|{f['function'] for f in r['matched_changed_bodies']});known=collections.Counter(functions[f]['class'] for f in fs);cl='C' if known['C'] else 'B' if known['B'] else 'A' if known['A-function']==len(fs) and not r['unresolved_edge_count'] else 'D'
 result.append(dict(id=r['id'],name=r['name'],**{'class':cl},class_counts=dict(known),changed_functions=[dict(function=x['function'],classification=functions[x['function']]['class'],source_ref='classification/functions.json.xz#'+x['function']) for x in r['matched_changed_bodies']],functions=fs,unresolved_edges=r['unresolved_edge_count'],unmatched_function_identities=r['unmatched_function_identities'],suspension='RETAINED',rerun={'structural':'pending' if cl in ['B','C'] else 'not required until source identity resolved','native_differential':'pending' if cl in ['B','C'] else 'not required until source identity resolved'},note='B/C records demonstrated source drift, not completeness; unresolved function/edge inventory retained. No A without identity of every reached body.'))
with lzma.open(O/'functions.json.xz','wt') as h:json.dump(functions,h,indent=2)
(O/'draft-rows.json').write_text(json.dumps(result,indent=2)+'\n')
print('rows',collections.Counter(r['class'] for r in result),'functions',collections.Counter(r['class'] for r in functions.values()))
for r in result:print(r['id'],r['class'],r['class_counts'])
print('source diffs retained in functions.json.xz')
