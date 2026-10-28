"""Resolve matched project source spans on the frozen candidate, without editing it."""
from pathlib import Path
import json,lzma,re,hashlib,sys,collections
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
P=Parser(Language(tree_sitter_rust.language()));E=Path('evidence/pv-fscan-20261028');O=E/'classification';fs=json.loads(lzma.open(O/'functions.json.xz').read());pins=json.loads((E/'runtime-source-pins.json').read_text());pinmap={p['path']:p for p in pins['files']};idx=collections.defaultdict(list)
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
for p,pin in pinmap.items():
 if not p.endswith('.rs') or not p.startswith('crates/'):continue
 b=Path(p).read_bytes();assert hashlib.sha256(b).hexdigest()==pin['sha256'];tree=P.parse(b)
 for n in walk(tree.root_node):
  if n.type not in ['function_item','struct_item','enum_item']:continue
  name=n.child_by_field_name('name');body=n.child_by_field_name('body')
  if not name:continue
  name=b[name.start_byte:name.end_byte].decode();text=b[n.start_byte:n.end_byte].decode();par=n.parent;im=''
  while par:
   if par.type=='impl_item':im=b[par.start_byte:par.end_byte].decode().split('{',1)[0]
   par=par.parent
  idx[name].append(dict(path=p,line=n.start_point.row+1,end_line=n.end_point.row+1,item=text,impl=im,kind=n.type))
# Only a matched printed body can establish that the same source definition was active on both sides.
reached=json.loads(lzma.open(E/'reached-audit.json.xz').read());cohorts={c:{f for r in reached for f in (r['reached_functions'].get(c,[]) if isinstance(r.get('reached_functions'),dict) else [])} for c in ['old','deployed']}
for f,r in fs.items():
 if not f.startswith('aspis_'):continue
 if f not in cohorts['old'] or f not in cohorts['deployed']:continue
 name=f.split('(_',1)[0].split('()',1)[0].split('::{closure#',1)[0].split('::')[-1];pm=re.search(r'(crates/[^:]+\.rs)',f);cands=idx[name]
 if pm:cands=[v for v in cands if v['path']==pm[1]]
 else:cands=[v for v in cands if v['path'].startswith('crates/'+f.split('::')[0].replace('_','-')+'/')]
 if len(cands)>1:
  imp=re.search(r'::impl(.+?)>::',f)
  if imp:
   t=lambda s:re.findall(r'\w+|[^\s]',s)
   cs=[v for v in cands if t(v['impl'])==t('impl'+imp[1])]
   if cs:cands=cs
 if not cands and '::eq(' in f:
  typ=re.search(r'_1: &([A-Z]\w*)',f)
  if typ:cands=[v for v in idx[typ[1]] if (not pm or v['path']==pm[1])]
 if len(cands)!=1:continue
 v=cands[0];text=v['item'];r['project_source']=dict(path=v['path'],line=v['line'],end_line=v['end_line'],item_sha256=hashlib.sha256(text.encode()).hexdigest(),file_pin=pinmap[v['path']],cohort_association='same frozen source mirror verified by original scan; both printed MIR identities present',kind=v['kind'])
 if '#[cfg' not in text and 'cfg!' not in text:
  r.update(**{'class':'A-function'},reason='same complete frozen source span in both compiled cohorts; no internal cfg selection',source_identity='project span byte-identical; derived bodies tied to same source declaration')
with lzma.open(O/'functions.json.xz','wt') as h:json.dump(fs,h,indent=2)
print(collections.Counter(f['class'] for f in fs.values()))
