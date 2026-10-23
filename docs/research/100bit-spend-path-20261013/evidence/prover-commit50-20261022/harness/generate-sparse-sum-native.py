from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
(E/'native/sparse-sum.rs').write_text('''
mod sparse_sum_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct K(u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Trace{n:usize,args:[(u8,u32,u32);2],answers:[u32;2]}
impl Trace{fn call(&mut self,o:u8,a:K,b:K)->K{let i=self.n;self.n+=1;self.args[i]=(o,a.0,b.0);K(self.answers[i])}}
fn native(column:[K;1024],sum:K,row:usize,weight:K,t:&mut Trace)->K {
 let product=t.call(0,weight,column[row]);t.call(1,sum,product)
}
fn owner(column:[K;1024],pref:usize,left:u16,acc:K,row:usize,weight:K,t:&mut Trace)->(K,usize,u16){
 let value=column[row];let product=t.call(0,weight,value);
 let next=pref.wrapping_add(1);let remaining=left-1;
 (t.call(1,acc,product),next,remaining)
}
#[cfg(kani)] mod proofs{use super::*;
 #[kani::proof] #[kani::unwind(1030)] fn iteration(){
  let raw:[u32;1024]=kani::any();let column=raw.map(K);
  let pref:usize=kani::any();let left:u16=kani::any();let row:usize=kani::any();
  kani::assume(pref<1024 && left>0 && left<=1024 && row<1024);
  let acc=K(kani::any());let weight=K(kani::any());let mut a=Trace{n:0,args:[(0,0,0);2],answers:kani::any()};let mut b=a;
  let x=native(column,acc,row,weight,&mut a);let y=owner(column,pref,left,acc,row,weight,&mut b);
  assert_eq!(x,y.0);assert_eq!(pref+1,y.1);assert_eq!(left-1,y.2);assert_eq!(a,b);
 }
}
}
''')
p=E/'native/lib.rs';p.write_text(p.read_text()+'\ninclude!("sparse-sum.rs");\n')
p=Path('crates/aspis-statement/src/constraints_v4.rs')
(E/'pins/sparse-sum-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),lines=[782,793],abstractions='Complete 1024-entry column context, source Vec iterator weighted-sum transition versus owned counter continuation, arbitrary paired proven-weight and row outputs. Exact selected column read and QM31 multiplication/addition operands and order. Verified weight/address helpers justify callee answers; source scanner/Vec emissions are still explicit caller obligations.'),indent=2)+'\n')
