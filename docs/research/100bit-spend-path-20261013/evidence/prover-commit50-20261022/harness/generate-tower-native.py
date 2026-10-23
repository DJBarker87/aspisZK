from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
(E/'native/tower.rs').write_text('''
mod tower_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct C{a:u32,b:u32}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct K{c0:C,c1:C}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct Trace{n:usize,args:[(u8,u32,u32);3],answers:[[u32;2];3]}
impl Trace{fn i(&mut self,x:C)->C{let i=self.n;self.n+=1;self.args[i]=(0,x.b,0);C{a:self.answers[i][0],b:x.a}}fn r(&mut self,x:C)->C{let i=self.n;self.n+=1;self.args[i]=(1,x.a,x.b);C{a:self.answers[i][0],b:self.answers[i][1]}}}
fn native(x:K,coordinate:usize,t:&mut Trace)->K{match coordinate{0=>x,1=>K{c0:t.i(x.c0),c1:t.i(x.c1)},2=>K{c0:t.r(x.c1),c1:x.c0},3=>{let r=t.r(x.c1);K{c0:t.i(r),c1:t.i(x.c0)}},_=>panic!()}}
fn owner(x:K,coordinate:u8,t:&mut Trace)->K{if coordinate==0{x}else if coordinate==1{K{c0:t.i(x.c0),c1:t.i(x.c1)}}else if coordinate==2{K{c0:t.r(x.c1),c1:x.c0}}else if coordinate==3{let r=t.r(x.c1);K{c0:t.i(r),c1:t.i(x.c0)}}else{panic!()}}

#[cfg(kani)]mod proofs{use super::*;
 #[kani::proof]#[kani::unwind(6)]fn tower(){
 let r:[u32;4]=kani::any();let x=K{c0:C{a:r[0],b:r[1]},c1:C{a:r[2],b:r[3]}};let j:usize=kani::any();kani::assume(j<4);
 let mut a=Trace{n:0,args:[(0,0,0);3],answers:kani::any()};let mut b=a;
 let z=native(x,j,&mut a);let w=owner(x,j as u8,&mut b);assert_eq!(z,w);assert_eq!(a,b);
 }
}
}
''');p=E/'native/lib.rs';p.write_text(p.read_text()+'\ninclude!("tower.rs");\n')
p=Path('crates/aspis-core/src/state_only_hiding.rs');(E/'pins/tower-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),lines=[436,468],abstractions='Complete four-kind QM31 basis dispatch and outputs, usize-to-u8 narrowing for legal coordinates. cm_i negative limb answer and CM mul_r are universal paired verified callees with all operands and order retained; canonical arithmetic value is separately proved.'),indent=2)+'\n')
