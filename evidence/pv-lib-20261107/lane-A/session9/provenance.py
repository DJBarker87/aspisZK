"""Source and typed-metadata provenance. No default allocator inference."""
from pathlib import Path
import hashlib,json,lzma,runpy,sys
E=Path(__file__).parent
ns=runpy.run_path(str(E/'inspect-metadata.py'));p,n=ns['p'],ns['normal'];p=n(p)
sha=lambda b:hashlib.sha256(b).hexdigest()
def statement(fid,sid):
 found=[]
 def walk(x):
  if isinstance(x,dict):
   if x.get('id')==sid and 'kind'in x:found.append(x)
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(p['fun_decls'][fid]['body']);assert len(found)==1;return found[0]
G={'Adt':{'id':{'Adt':1},'generics':dict(regions=[],types=[],const_generics=[],trait_refs=[])}}
a=statement(218,9167);assert a['kind']['Assign'][1]['Aggregate'][0]['Adt'][0]==G['Adt']
b=statement(218,9170)['kind']['Call']['call'];assert b['func']['Regular']['generics']['types'][1]==G
c=statement(315,11160)['kind']['Assign'][1]['Aggregate'];assert len(c[1])==3;assert c[1][2]['Move']['ty']=={'TypeVar':{'Free':1}}
assert statement(315,11159)['kind']['Assign'][1]['Use'][0]['Move']['kind']=={'Local':2}
option=p['type_decls'][17]['kind']['Enum'];assert [(v['id'],v['name'],len(v['fields']))for v in option]==[(0,'None',0),(1,'Some',1)]
assert option[1]['fields'][0]['ty']=={'TypeVar':{'Free':0}}
S=lzma.decompress((E/'rust-1.94.1-alloc-src-sync.rs.xz').read_bytes()).decode()
for text in ['A: Allocator = Global','Self::from_inner_in(ptr, Global)','Self { ptr, phantom: PhantomData, alloc }','let _weak = Weak { ptr: self.ptr, alloc: &self.alloc };']:
 assert text in S,text
r=dict(inputs=[dict(path=str(f),compressed_sha256=sha(f.read_bytes()),raw_sha256=sha(lzma.decompress(f.read_bytes())))for f in [E.parent/'session5/thread-llbc.json.xz',E.parent/'session7/NativeInstructions.json.xz',*sorted(E.glob('rust-*.xz'))]],
 metadata=dict(Option=p['type_decls'][17],Global=p['type_decls'][1],Arc=p['type_decls'][21],Option_glue=p['fun_decls'][157],constructor_chain=[statement(124,5005),a,statement(218,9170),statement(315,11159),statement(315,11160)],glue405=p['trait_impls'][76]),
 structural_binding=['1.94.1 Arc::new -> from_inner -> from_inner_in(ptr, Global)','retained f124/5005 -> f218; f218/9167 constructs Global ADT1;9170 passes it as A to315','f315/11159 moves allocator ARG2 to local5;11160 moves local5 to Arc field2','the erased Arc type alone supplies NO A; the actual tagged allocator field is required','Option variant0 has no field and variant1 drops its sole T field by Rust enum drop semantics'],
 evidence_class='script-checked structural/source provenance plus typed accepted-emission binding; source-to-binary compiler preservation retained under V370',
 new_trust_fields=0,endpoint_premises_added=0,allocation_byte_images_defined=0)
q=E/'PROVENANCE.json'
if '--check'in sys.argv:assert json.loads(q.read_text())==r
else:q.write_text(json.dumps(r,indent=2)+'\n')
print('Option157 and allocator constructor provenance checked')
