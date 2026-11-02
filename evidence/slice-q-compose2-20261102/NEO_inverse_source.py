"""Exact deployed addition-chain erasure; no arithmetic body is replaced by a claim."""
from pathlib import Path
import sys,json,subprocess,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-q-fnptr-20261029'))
from NEF_OBSERVER_CERTIFICATE import tok,functions

def replace_one(a,old,new):
 hits=[i for i in range(len(a)-len(old)+1) if a[i:i+len(old)]==old];assert len(hits)==1,('erasure occurrence',old,hits)
 i=hits[0];return a[:i]+new+a[i+len(old):]
def normalize(ts):
 out=[];i=0
 while i<len(ts):
  if ts[i] not in ['NEO_inv_product','NEO_inv_square']:out.append(ts[i]);i+=1;continue
  name=ts[i];assert ts[i+1]=='(';depth=1;j=i+2;start=j;args=[]
  while depth:
   t=ts[j]
   if t=='(':depth+=1
   elif t==')':depth-=1
   if t==',' and depth==1:args.append(ts[start:j]);start=j+1
   if depth==0:args.append(ts[start:j]);break
   j+=1
  assert len(args)==3 and args[2]==['&','mut','log']
  a,b=normalize(args[0]),normalize(args[1])
  out+=(a+['.','mul','(']+b+[')']) if name=='NEO_inv_product' else (['square_n','(']+a+[',']+b+[')'])
  i=j+1
 return out

def check(source):
 frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],cwd=R,text=True)
 candidates=[b for h,b in functions(frozen)['inv'] if 't2' in b];assert len(candidates)==1
 original=replace_one(candidates[0],tok('#[cfg(feature="r0-op-count")] let _count=crate::r0_op_count::enter(crate::r0_op_count::Op::FInv);'),[])
 helper=functions(source)['NEO_inverse_log'];assert len(helper)==1
 code=replace_one(helper[0][1],tok('let mut log=NEO_InvLog{kind:[0;17],a:[0;17],b:[0;17],result:[0;17],used:0};'),[])
 code=normalize(code);at=next(i for i in range(len(code)-2) if code[i:i+3]==['let','out','='])
 assert code[-6:]==[';','(','out',',','log',')']
 code=code[:at]+code[at+3:-6];code=['self' if t=='x' else t for t in code]
 assert code==original,'changed source DAG under erasure'
 assert not any(t in source for t in ['static mut','Option<fn','proof_for_contract','stub_verified'])
 return dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',body_tokens_sha256=hashlib.sha256(json.dumps(original).encode()).hexdigest(),helper_sha256=hashlib.sha256(source.encode()).hexdigest(),local_record=True,exact_erasure=True,product_pair='LPf_BaseMultiply.source: all raw U32; exact natural product reply',square_pair='NEB_SquareDomains.source / NEB_SquareComposition.loop_frame: same count in {2,4,8}; exact emitted reply selects one canonical oracle reply',whole_inverse_credit=False)
if __name__=='__main__':
 src=(E/'NEO_inverse.rs.txt').read_text();out=check(src);mut=[]
 for label,a,b in [('count','t8,8,&mut log','t8,4,&mut log'),('right operand','t24,4,&mut log),t4','t24,4,&mut log),t8'),('input','NEO_inv_product(x,x,','NEO_inv_product(x,M31::ONE,'),('output','NEO_inv_product(t30,t30,','NEO_inv_product(t29,t30,')]:
  assert a in src,label
  try:check(src.replace(a,b,1))
  except AssertionError:mut.append(dict(test=label,rejected=True))
  else:raise AssertionError('mutation admitted: '+label)
 (E/'NEO_INVERSE_SOURCE.json').write_text(json.dumps(dict(certificate=out,mutations=mut),indent=1)+'\n');print(json.dumps(dict(positive=True,mutations=len(mut))))
