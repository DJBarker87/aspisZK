from pathlib import Path
import json,hashlib,subprocess,re,difflib
E=Path(__file__).resolve().parent
x=json.loads((E/'NHH_NATIVE_INPUTS.json').read_text())
source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],text=True)
def body(name):
 m=re.search(r'pub fn '+name+r'\(',source);a=source.index('{',m.end());i=a+1;d=1
 while d:d+=(source[i]=='{')-(source[i]=='}');i+=1
 return source[a+1:i-1]
original=body('inv_with')
instrumented=original.replace('self','input').replace('self.a','input.a')
for term,repl in [('input.a.mul(input.a)','NHH_product(log,input.a,input.a)'),('input.b.mul(input.b)','NHH_product(log,input.b,input.b)'),('input.a.mul(inv_norm)','NHH_product(log,input.a,inv_norm)'),('input.b.neg().mul(inv_norm)','NHH_product(log,input.b.neg(),inv_norm)'),('inverse(norm)','NHH_backend(log,norm)')]:instrumented=instrumented.replace(term,repl)
erased=instrumented
for term,repl in [('NHH_product(log,input.a,input.a)','input.a.mul(input.a)'),('NHH_product(log,input.b,input.b)','input.b.mul(input.b)'),('NHH_product(log,input.a,inv_norm)','input.a.mul(inv_norm)'),('NHH_product(log,input.b.neg(),inv_norm)','input.b.neg().mul(inv_norm)'),('NHH_backend(log,norm)','inverse(norm)')]:erased=erased.replace(term,repl)
assert erased.replace('input','self')==original
s='\n#[derive(Clone,Copy)]\nstruct NHH_Event{kind:u8,a:M31,b:M31,out:M31}\nstruct NHH_Log{events:[NHH_Event;5],len:usize}\nfn NHH_event(log:&mut NHH_Log,kind:u8,a:M31,b:M31)->M31{\n assert!(a.0<P&&b.0<P&&log.len<5);\n let out=M31(kani::any());kani::assume(out.0<P);\n log.events[log.len]=NHH_Event{kind,a,b,out};log.len+=1;out\n}\nfn NHH_product(log:&mut NHH_Log,a:M31,b:M31)->M31{NHH_event(log,0,a,b)}\nfn NHH_backend(log:&mut NHH_Log,a:M31)->M31{NHH_event(log,1,a,M31(0))}\nfn NHH_fixed(log:&mut NHH_Log,input:CM31)->CM31{\n'+instrumented+'\n}\n'
s+='\n#[kani::proof]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::unwind(80)]\nfn cm_inverse_log(){\n let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P&&(a!=0||b!=0));\n let input=CM31{a:M31(a),b:M31(b)};\n let e=NHH_Event{kind:0,a:M31(0),b:M31(0),out:M31(0)};\n let mut log=NHH_Log{events:[e;5],len:0};let out=NHH_fixed(&mut log,input);\n let n=log.events[0].out.add(log.events[1].out);let inv=log.events[2].out;\n let property=log.len==5&&log.events[0].kind==0&&log.events[0].a==input.a&&log.events[0].b==input.a&&\n log.events[1].kind==0&&log.events[1].a==input.b&&log.events[1].b==input.b&&\n log.events[2].kind==1&&log.events[2].a==n&&log.events[2].b==M31(0)&&\n log.events[3].kind==0&&log.events[3].a==input.a&&log.events[3].b==inv&&\n log.events[4].kind==0&&log.events[4].a==input.b.neg()&&log.events[4].b==inv&&\n out.a==log.events[3].out&&out.b==log.events[4].out;\n check(property);\n}\n'
x['crates/aspis-r1-cost-probe/src/NHH_fields.rs']+=s
(E/'NHH_fields_inverse.rs.txt').write_text(x['crates/aspis-r1-cost-probe/src/NHH_fields.rs'])
(E/'NHH_INVERSE_INPUTS.json').write_text(json.dumps(x))
(E/'NHH_INVERSE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()},indent=1)+'\n')
(E/'NHH_INVERSE_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',function='CM31::inv_with(M31::inv)',original_body_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_body_sha256=hashlib.sha256(instrumented.encode()).hexdigest(),erasure_equal=True,backend_specialization='Fixed direct M31::inv only; no generic callback credit',opaque_sites=['aa=a*a','bb=b*b','inverse(norm)','real=a*inverse','imag=(-b)*inverse'],unchanged_calls=['M31.add','M31.neg']),indent=1)+'\n')
