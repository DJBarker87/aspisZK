"""Source-only callback/drop inspection. Native integration is still open."""
from pathlib import Path
import json,hashlib,subprocess,re,sys
E=Path('evidence/pv-evh10-20261102');sha=lambda b:hashlib.sha256(b).hexdigest()
def source(p):return subprocess.check_output(['git','show','HEAD:'+p]).decode()
def body(t,a):
 start=t.index(a);i=t.index('{',start);j=i+1;n=1
 while n:
  n+=(t[j]=='{')-(t[j]=='}');j+=1
 return t[i:j]
plain=[('crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs','PoolV1PairHidingLayoutErrorV1'),('crates/aspis-prover/src/state_only_hiding.rs','StateOnlyMaskBuildError'),('crates/aspis-core/src/r0/mod.rs','Error'),('crates/aspis-r1-cost-probe/src/compact.rs','CodecError')]
types=[]
for p,name in plain:
 t=source(p);a=t.index('pub enum '+name);pre=t[max(0,a-100):a];assert re.search(r'#\[derive\([^]]*\bCopy\b',pre)
 b=body(t,'pub enum '+name)
 assert not re.search(r'impl(?:<[^>]+>)?\s+(?:core::ops::)?Drop\s+for\s+'+name+r'\b',t)
 types.append(dict(path=p,sha256=sha(t.encode()),type=name,body=b,drop_reason='Copy payloads; no user Drop; source destructor has no resource calls'))
std=json.load(open(E/'callback-stdlib-source.json'))
for v in std:assert sha(v['text'].encode())==v['sha256']
c=std[0]['text'];l=std[1]['text']
assert ''.join(body(c,'pub struct TryReserveError').split())=='{kind:TryReserveErrorKind,}'
kind=body(c,'pub enum TryReserveErrorKind')
assert 'CapacityOverflow,' in kind and 'layout: Layout,' in kind and 'non_exhaustive: (),' in kind
assert not re.search(r'impl\s+Drop\s+for\s+TryReserveError',c)
assert re.search(r'#\[derive\([^]]*\bCopy\b',l[l.index('pub struct Layout')-140:l.index('pub struct Layout')])
prep=json.load(open(E/'prepare-PV_EVH_NativeEntropyAdmission.json'))['result']
extracted=next(v['source'] for v in prep['project_checks'] if v['module']=='R1Z.ProverRwFullTypes')
raw=subprocess.check_output(['git','show',extracted['revision']+':'+extracted['path']]);assert sha(raw)==extracted['source_sha256']
lt=raw.decode()
records=[]
specs=[(0,'state_only_hiding','build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref','StateOnlyMaskBuildError::Layout',0),(1,'state_only_hiding','apply_pool_v1_pair_forest_mask_material_v1','StateOnlyMaskBuildError::Layout',0),(2,'prover','derive_private_salts','Error::Allocation',0),(4,'prover','prepare_opening','Error::Allocation',0),(5,'prover','publish_compact','Error::Semantic',0),(6,'prover','publish_compact','Error::Semantic',1),(7,'prover','derive_private_salt_step','Error::Semantic',0)]
for number,cratefile,fn,result,occ in specs:
 p=('crates/aspis-prover/src/' if cratefile=='state_only_hiding' else 'crates/aspis-r1-cost-probe/src/')+cratefile+'.rs';t=source(p);b=body(t,'fn '+fn+'(')
 compact=''.join(b.split());token='.map_err(|_|'+result+')';assert compact.count(token)>occ
 closure=('aspis_prover.state_only_hiding.' if cratefile=='state_only_hiding' else 'prover.')+fn+'.closure'+('_1' if number==6 else '')
 m=re.search(r'^def '+re.escape(closure)+r'(?=\s)',lt,re.M);assert m,closure
 tail=lt[m.end():m.end()+180]
 assert re.match(r'\s*(?:\(T0 : Type\))?\s*:=\s*Unit\b',tail),closure
 records.append(dict(extracted_closure=closure,callback=number,path=p,sha256=sha(t.encode()),function=fn,function_body_sha256=sha(b.encode()),lambda_tokens=token,occurrence=occ,capture='empty: discarded argument and fixed enum constructor only',consumed_argument='TryReserveError with scalar Layout fields' if number==2 else 'Copy enum',unused_closure_drop='empty capture, no owned fields',native_installation='OPEN'))
result=dict(status='source-only inspection; no new callback/native theorem claimed',evidence_class='structural source inspection (own-1)',records=records,extracted_types=extracted,copy_types=types,stdlib=[{k:v for k,v in q.items() if k!='text'} for q in std],
 retained=['source-to-machine V370','retired/register/spill/copy L3 observer','actual Frames.invoke/drop and seven RuntimeCallbackCtor native installations','unwinding and remaining callbacks'],rows_removed=[],trust_fields_added=[])
p=E/'callback-drop-source-inspection.json'
if '--check' in sys.argv:assert json.load(open(p))==result
else:p.write_text(json.dumps(result,indent=2)+'\n')
print('PASS seven callback source captures and payload/drop inspection; native installation OPEN')
