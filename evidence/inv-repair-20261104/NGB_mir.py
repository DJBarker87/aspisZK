"""Read-only MIR/source census. No compiler, host or historical producer mutation."""
import sys,pathlib,json,lzma,hashlib,re,collections,subprocess
sys.dont_write_bytecode=True
sys.path.insert(0,'/private/tmp/NFZ-parser-20261104')
from tree_sitter import Language,Parser
import tree_sitter_rust
E=pathlib.Path(__file__).resolve().parent; R=E.parents[1]; Z=R/'evidence/inv-defects-20261104'
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda b:hashlib.sha256(b).hexdigest()
files=json.loads(lzma.open(Z/'NFZ_FROZEN_SOURCE.json.xz').read())
parser=Parser(Language(tree_sitter_rust.language()))
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def txt(n,b):return b[n.start_byte:n.end_byte].decode() if n else ''
def parents(n):
 while n.parent:n=n.parent;yield n
D=[]
for p,s in files.items():
 if not p.endswith('.rs'):continue
 # Independent git authority, not just trust in the NFZ payload.
 assert subprocess.check_output(['git','show',F+':'+p],cwd=R)==s.encode(),p
 b=s.encode();t=parser.parse(b)
 for n in walk(t.root_node):
  if n.type!='function_item' or n.child_by_field_name('body') is None:continue
  scopes=[];impl=None;trait=''
  for a in reversed(list(parents(n))):
   if a.type in ['mod_item','function_item']:scopes.append(txt(a.child_by_field_name('name'),b))
   if a.type=='impl_item':
    scopes.append(txt(a.child_by_field_name('type'),b));impl=a;trait=txt(a.child_by_field_name('trait'),b)
  name=txt(n.child_by_field_name('name'),b);key=p+'::'+'::'.join(scopes+[name]);body=n.child_by_field_name('body')
  calls=[]
  for a in walk(body):
   if a.type=='call_expression':
    fn=a.child_by_field_name('function');raw=txt(fn,b)
    calls.append(dict(line=a.start_point.row+1,expression=raw,text=txt(a,b)))
   # Function-valued arguments (map_err, map) are independent AST references.
   if a.type in ['identifier','scoped_identifier']:
    if txt(a,b) in ['error','extension_limbs']:calls.append(dict(line=a.start_point.row+1,expression=txt(a,b),text=txt(a,b)))
  D.append(dict(function=key,file=p,name=name,trait=trait,start=n.start_point.row+1,end=n.end_point.row+1,impl_start=impl.start_point.row+1 if impl else None,body_range=[body.start_byte,body.end_byte],body_sha256=sha(b[body.start_byte:body.end_byte]),calls=calls))
C=json.loads((Z/'NFZ_CANDIDATES.json').read_text())['candidates']
core='crates/aspis-core/src/'
TARGETS={c['to'] for c in C if c.get('to')}|{core+'field.rs::QM31::'+x for x in ['sub','mul']}
TARGETS|={core+'r0/scalar.rs::'+x+'::from_m31' for x in ['M31','CM31','QM31','WideExact']}
# from_qm31 is a transitive child of the newly reached WideExact trait impl.
TARGETS.add(core+'field/wide_exact.rs::WideExact::from_qm31')
def source_target(c,owner):
 raw=c['expression'];raw=raw.replace('Self::',owner.split('::')[-2]+'::' if len(owner.split('::'))>2 else 'Self::')
 raw=raw.replace('aspis_core::','').replace('crate::','')
 if 'from_m31' in raw:
  if raw=='E::from_m31':return core+'r0/scalar.rs::WideExact::from_m31'
  m=re.search(r'<(\w+) as CodeField>::from_m31',raw)
  if m:return core+'r0/scalar.rs::'+m[1]+'::from_m31'
  if raw.endswith('CM31::from_m31'):return core+'field.rs::CM31::from_m31'
 if raw=='QM31::from_cm31':return core+'field.rs::QM31::from_cm31'
 if raw=='WideExact::from_qm31' or raw=='E::from_qm31':return core+'field/wide_exact.rs::WideExact::from_qm31'
 if raw.startswith('<$t>::'):return core+'field.rs::QM31::'+raw.split('::')[-1]
 if raw.endswith('circle_fallback_point'):return core+'transcript.rs::circle_fallback_point'
 if raw=='error':return 'programs/r1-cost-probe/src/lib.rs::error'
 if raw=='extension_limbs':return 'crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs'
 if raw.endswith(('.sub','.mul','::sub','::mul')):
  return core+'field.rs::QM31::'+re.split(r'[.:]',raw)[-1]
 if False:
  meth=raw.rsplit('.',1)[1]
  # Concrete K alias and receiver chains in Weights::new only.
  if owner=='crates/aspis-r1-cost-probe/src/weights.rs::Weights::new':return core+'field.rs::QM31::'+meth
 return None

def mir_target(l):
 m=re.search(r'<(M31|CM31|QM31|WideExact) as (?:aspis_core::r0::)?CodeField>::from_m31\(',l)
 if m:return core+'r0/scalar.rs::'+m[1]+'::from_m31'
 for target in sorted(TARGETS,key=len,reverse=True):
  tail=target.split('::',1)[1]
  if '/r0/scalar.rs' in target:continue
  if re.search(r'(?<![\w:])'+re.escape(tail)+r'\(',l):return target
 # Named function items supplied to combinators.
 if '{error}>' in l:return 'programs/r1-cost-probe/src/lib.rs::error'
 if '{extension_limbs}>' in l:return 'crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs'
 return None

def caller(header,crate):
 h=header[3:].split('(')[0];name=h.split('::')[-1];name=name.split('<')[0]
 impl=re.search(r'<impl at ([^:]+):(\d+):',header)
 closure=re.search(r'closure@([^:]+):(\d+):',header)
 if closure:
  p,line=closure[1],int(closure[2]);ds=[d for d in D if d['file']==p and d['start']<=line<=d['end']]
 elif impl:
  p,line=impl[1],int(impl[2]);ds=[d for d in D if d['file']==p and d['impl_start']==line and d['name']==name]
 else:
  prefix={'program':'programs/r1-cost-probe/src/','library':'crates/aspis-r1-cost-probe/src/','core':core}[crate]
  ds=[d for d in D if d['file'].startswith(prefix) and d['name']==name]
  if len(ds)>1:
   qualified=[d for d in ds if (d['file'].removeprefix(prefix).removesuffix('.rs').replace('/','::')+'::'+d['function'].split('::',1)[1])==h]
   if qualified:ds=qualified
  if len(ds)>1:
   q=h.replace('::','/');ds2=[d for d in ds if d['file'].removeprefix(prefix).removesuffix('.rs') in q]
   if ds2:ds=ds2
 if len(ds)==1:return ds[0]
 if impl and name in ['sub','mul'] and impl[1].endswith('r0/scalar.rs'):
  p=impl[1];line=int(impl[2]);owner={41:'M31',56:'CM31',70:'QM31',87:'WideExact'}[line]
  return dict(function=p+'::'+owner+'::'+name,file=p,calls=[dict(line=29 if name=='sub' else 35,expression='<$t>::'+name,text='arithmetic!('+owner+'); expands scalar.rs macro')])
 return None

paths=[('program',Z/'LEAD_B006/aspis_r1_cost_probe_program.mir.xz'),('library',Z/'NFZ_B005_aspis_r1_cost_probe-2af8d844c3814c6b.mir.xz'),('core',Z/'NFZ_aspis_core.mir.xz')]
records=[];pins=[];headers={}
for crate,p in paths:
 raw=lzma.open(p).read();pins.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),uncompressed_sha256=sha(raw)))
 header='';d=None;heads=[]
 for i,l in enumerate(raw.decode().splitlines(),1):
  if l.startswith('fn '):header=l;d=caller(header,crate);heads.append(dict(line=i,header=l,source_function=d['function'] if d else None))
  if ' -> [' not in l or ' = ' not in l:continue
  target=mir_target(l)
  # Retain symbolic trait-dispatch sites as such, never instantiate E/T by guess.
  symbolic=re.search(r'<(E|T) as CodeField>::from_m31\(',l)
  if not target and not symbolic:continue
  sites=[c for c in d['calls'] if source_target(c,d['function'])==target] if d and target else []
  if symbolic and d:sites=[c for c in d['calls'] if c['expression'].endswith('::from_m31')]
  records.append(dict(id=f'NGB_M{len(records)+1:04}',mir=p.name,mir_path=str(p.relative_to(R)),mir_line=i,caller_header=header,caller=d['function'] if d else None,callee=target or f'<{symbolic[1]} as CodeField>::from_m31',mir_text=l.strip(),source_file=d['file'] if d else None,source_sites=sites,source_check='AGREES' if sites else 'UNRESOLVED_NOT_ADMITTED',features=['pool-adapter','private-leaf-salts'],prover=False,feature_scope='program root feature selection; core MIR uses r0 per NFZ_CORE_MIR_REVIEW',generic_uninstantiated=bool(symbolic)))
 headers[crate]=heads
out=dict(frozen_revision=F,inputs=pins,parser={'tree-sitter':'0.25.2','tree-sitter-rust':'0.24.2'},targets=sorted(TARGETS),source_authority='tree-sitter AST of NFZ frozen payload, every Rust file compared byte-for-byte with git frozen revision',edges=records,counts=dict(total=len(records),source_agrees=sum(x['source_check']=='AGREES' for x in records)))
(E/'NGB_MIR_EDGES.json').write_text(json.dumps(out,indent=1)+'\n')
# Expose AST declarations for the prefix-owned additive producer.
ast=(json.dumps(D,indent=1)+'\n').encode()
(E/'NGB_SOURCE_AST.json.xz').write_bytes(lzma.compress(ast))
(E/'NGB_SOURCE_AST.json.sha256').write_text(sha(ast)+'\n')
print(json.dumps(out['counts']))
print('unresolved',[(x['id'],x['caller'],x['callee']) for x in records if x['source_check']!='AGREES'])
