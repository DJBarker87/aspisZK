from pathlib import Path
import runpy,json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
old=runpy.run_path(str(E.parent/'native-front1b-20261028/NDL_sources.py'))['sources']()
def fn(s,n):
 i=s.index('fn '+n+'(');j=s.index('{',i)+1;d=1
 while d:d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i:j]
ref='\n'.join('pub '+fn(old['NDL_reference.rs'],n) for n in ['add_ref','sub_ref','double_observed_ref'])+'\n'
(E/'NGM_double_reference.rs.txt').write_text(ref)
inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());s=inputs[C+'NGM_weights.rs']
s+='\nmod double_reference{include!("NGM_double_reference.rs");}\n'
s+='''struct ProductLog{replies:[K;2],left:[K;2],right:[K;2],count:usize}
fn opaque_product(x:K,y:K,log:&mut ProductLog)->K{let i=log.count;log.left[i]=x;log.right[i]=y;log.count+=1;log.replies[i]}
fn source_double(x:K,log:&mut ProductLog)->K{opaque_product(x,x,log).add(opaque_product(x,x,log)).sub(K::ONE)}
fn canonical_q()->K{let x:[u32;4]=kani::any();for word in x{kani::assume(word<0x7fffffff);}fromq(x)}
fn exercise_double(group:u8){let x=canonical_q();let mut log=ProductLog{replies:[canonical_q(),canonical_q()],left:[K::ZERO;2],right:[K::ZERO;2],count:0};let expected=double_reference::double_observed_ref(qwords(log.replies[0]),qwords(log.replies[1]));let out=qwords(source_double(x,&mut log));let good=match group{0=>out[0]==expected[0],1=>out[1]==expected[1],2=>out[2]==expected[2],3=>out[3]==expected[3],4=>log.count==2,5=>log.left[0]==x&&log.right[0]==x,6=>log.left[1]==x&&log.right[1]==x,_=>false};assert!(good != cfg!(NGM_invert));}
macro_rules! double_gate{($n:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(17)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]fn $n(){exercise_double($g)}};}
'''
for g in range(7):s+=f'double_gate!(double_control_{g},{g});\n'
inputs[C+'NGM_weights.rs']=s;inputs[C+'NGM_double_reference.rs']=ref
(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NGM_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in inputs.items()});(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
(E/'NGM_DOUBLE_ASSOCIATION.json').write_text(json.dumps(dict(frozen_body='pub fn double(x:K)->K { x.mul(x).add(x.mul(x)).sub(K::ONE) }',native_method='one source-fission scalar helper; two local typed opaque product calls, arbitrary canonical product replies; SAME operands captured; no multiplication executed',model='NGM_DoubleProduct.total supplies deterministic same-input reply; NGM_DoubleModel.observed supplies exact emitted function result',reference='verbatim add_ref/sub_ref/double_observed_ref from NDL source patch; freshly extracted as NGM_DoubleRef'),indent=2)+'\n')
