"""Explicit source associations for reexports and generated arch namespaces."""
from pathlib import Path
import json,lzma,re,sys,hashlib,difflib
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
P=Parser(Language(tree_sitter_rust.language()));E=Path('evidence/pv-fscan-20261028');O=E/'classification';fs=json.loads(lzma.open(O/'functions.json.xz').read());sources=json.loads(lzma.open(O/'sources.json.xz').read())['files']
paths={'_mm_blend_epi16':'stdarch/crates/core_arch/src/x86/sse41.rs','_mm_set_epi32':'stdarch/crates/core_arch/src/x86/sse2.rs','_mm_sha256msg1_epu32':'stdarch/crates/core_arch/src/x86/sha.rs','_mm_sha256msg2_epu32':'stdarch/crates/core_arch/src/x86/sha.rs','_mm_sha256rnds2_epu32':'stdarch/crates/core_arch/src/x86/sha.rs','_mm_add_epi32':'stdarch/crates/core_arch/src/x86/sse2.rs','_mm_set_epi64x':'stdarch/crates/core_arch/src/x86_64/sse2.rs','_mm_shuffle_epi32':'stdarch/crates/core_arch/src/x86/sse2.rs','_mm_alignr_epi8':'stdarch/crates/core_arch/src/x86/ssse3.rs','_mm_shuffle_epi8':'stdarch/crates/core_arch/src/x86/ssse3.rs','collect':'core/src/iter/traits/iterator.rs','from_raw_parts':'core/src/slice/raw.rs','from_raw_parts_mut':'core/src/slice/raw.rs','rust_oom':'std/src/alloc.rs'}
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
for f,r in fs.items():
 if r['class']!='D':continue
 name=f.split('(_',1)[0].split('()',1)[0].split('::{closure#',1)[0].split('::')[-1]
 if name not in paths:continue
 pair={}
 for c in ['evidence','deployed']:
  key=c+'/library/'+paths[name];v=sources[key];b=v['text'].encode();tree=P.parse(b);ns=[n for n in walk(tree.root_node) if n.type=='function_item' and (a:=n.child_by_field_name('name')) and b[a.start_byte:a.end_byte].decode()==name]
  if len(ns)!=1:break
  n=ns[0];body=n.child_by_field_name('body')
  if not body:break
  item=b[n.start_byte:n.end_byte].decode();bb=b[body.start_byte:body.end_byte];pair[c]=dict(key=key,path=v['path'],line=n.start_point.row+1,end_line=n.end_point.row+1,file_sha256=v['sha256'],item_sha256=hashlib.sha256(item.encode()).hexdigest(),body_sha256=hashlib.sha256(bb).hexdigest(),item=item)
 if len(pair)!=2:continue
 a,b=pair['evidence'],pair['deployed'];r['source_evidence']={c:{k:v for k,v in v.items() if k!='item'} for c,v in pair.items()};r['manual_source_association']='Explicit reexport namespace to actual rust-src defining file; exactly one named definition per cohort.'
 if a['item']!=b['item']:
  r.update(**{'class':'B'},reason='actual installed library source differs',diff=''.join(difflib.unified_diff(a['item'].splitlines(True),b['item'].splitlines(True),fromfile=a['key'],tofile=b['key'])))
 elif '#[cfg' not in a['item'] and 'cfg!' not in a['item']:
  r.update(**{'class':'A-function'},reason='complete source item byte-identical across actual installed sources',source_identity='per-function source item byte-identical')
# The two barrier names are explicitly removed/added across the dependency versions.
for f,r in fs.items():
 if f.startswith('zeroize::') and f.split('::')[1].split('(')[0] in ['atomic_fence','optimization_barrier']:
  cand=r.get('candidates',{});present=[c for c,v in cand.items() if len(v)==1]
  if len(present)==1:
   r.update(**{'class':'C'},reason='dependency helper removed/added with blanket zeroize call change; complete source file retained in sources.json.xz')
   r['diff']='Definition present only in '+present[0]+': '+str(cand[present[0]][0])
with lzma.open(O/'functions.json.xz','wt') as h:json.dump(fs,h,indent=2)
