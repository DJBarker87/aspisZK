from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());s=x[C+'NGW_new.rs'];assert 'struct BoxLog'not in s
s+=r'''
struct BoxLog{allocated:*const Weights,calls:usize}
fn allocation(w:Weights,log:&mut BoxLog)->Box<Weights>{let out=Box::new(w);log.allocated=&*out;log.calls+=1;out}
fn source_box(variant:Variant,factors:Factors,points:[[K;10];3],extra:[K;2],log:&mut BoxLog)->Box<Weights>{allocation(Weights{variant,factors,points,extra},log)}
fn box_exercise(g:u8){let t:u8=kani::any();let v=match t%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};let f=arbitrary();let points=core::array::from_fn(|_|core::array::from_fn(|_|q(kani::any())));let extra=core::array::from_fn(|_|q(kani::any()));let k:usize=kani::any();kani::assume(k<5);let d:usize=kani::any();kani::assume(d<5);let term:usize=kani::any();kani::assume(term<4);let p:usize=kani::any();kani::assume(p<3);let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<2);let limb:usize=kani::any();kani::assume(limb<4);let mut log=BoxLog{allocated:core::ptr::null(),calls:0};
 let mut out=if g==4{source_box(v,f,points,extra,&mut log)}else{Weights::box_from_parts(v,f,points,extra)};
 if cfg!(NGW_invert){match g{0=>out.variant=if v==Variant::D{Variant::S2}else{Variant::D},1=>{let mut w=words(out.factors[k][d][term]);w[limb]^=1;out.factors[k][d][term]=q(w)},2=>{let mut w=words(out.points[p][i]);w[limb]^=1;out.points[p][i]=q(w)},3=>{let mut w=words(out.extra[j]);w[limb]^=1;out.extra[j]=q(w)},_=>{let different=Weights::box_from_parts(v,f,points,extra);assert!((&*different as *const Weights)==log.allocated);return;}}}
 assert!(match g{0=>out.variant==v,1=>words(out.factors[k][d][term])[limb]==words(f[k][d][term])[limb],2=>words(out.points[p][i])[limb]==words(points[p][i])[limb],3=>words(out.extra[j])[limb]==words(extra[j])[limb],_=>(&*out as *const Weights)==log.allocated&&log.calls==1&&log.allocated.cast::<K>()!=f.as_ptr().cast::<K>()&&log.allocated.cast::<K>()!=points.as_ptr().cast::<K>()});}
'''
for i in range(5):s+=f'gate!(box_g{i},box_exercise,{i});\n'
x[C+'NGW_new.rs']=s;(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
