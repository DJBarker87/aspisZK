"""Finite observations from exact mutable emissions; not a universal theorem."""
from pathlib import Path
import shutil,json,hashlib,re
T=Path('tools/pv-b3p6-20261028');D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=T/'v244-d18813';O.mkdir(exist_ok=True)
p=2147483647
q=lambda n:'{ c0 := { a := '+str(n%p)+'#u32, b := '+str((n*17)%p)+'#u32 }, c1 := { a := '+str((n*31)%p)+'#u32, b := '+str((n*47)%p)+'#u32 } }'
arr=lambda vals:'(Array.make '+str(len(vals))+'#usize ['+', '.join(vals)+'] (by rfl))'
for label,kind in [('Preweighted','add_preweighted'),('DigestStore','add_digest_binding'),('Pattern','pattern_values_literal'),('Active','active_literal')]:
 s='''import PV_B3P_P227_14
namespace PV_B3P_D18813'''+label+'''
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
-- Finite VM observations only; no kernel proof or native association claim.
def report {n : Usize} (r : Result (Array aspis_core.field.QM31 n)) : String :=
 match r with
 | .ok xs => reprStr (xs.val.flatMap (fun q => [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]))
 | .fail _ => "FAIL"
 | .div => "DIV"
'''
 for seed in [0,1,7,19]:
  n=(seed+1)*131;state=arr([q(n+i)for i in range(16)]);s+='def state'+str(seed)+' : Array aspis_core.field.QM31 16#usize := '+state+'\n'
  if label=='Preweighted':expr='reference_terminal.add_preweighted '+arr([q(n+i)for i in range(24)])+' 3#usize '+arr([q(seed+31+i)for i in range(7)])
  elif label=='DigestStore':expr='reference_terminal.add_digest_binding '+arr([q(n+i)for i in range(8)])+' ('+q(seed+13)+') state'+str(seed)+' 8#usize '+arr([str(seed+43+i)+'#u32'for i in range(8)])+' true'
  elif label=='Pattern':expr='reference_copy_terminal.pattern_values_literal state'+str(seed)+' ('+q(seed+17)+')'
  else:expr='(do let value ← reference_copy_terminal.Selectors.active_literal { high := '+arr([q(n+100+i)for i in range(64)])+', low := state'+str(seed)+' }; .ok '+arr(['value'])+')'
  s+='#eval "'+kind+':'+str(seed)+'=" ++ report ('+expr+')\n'
 s+='end PV_B3P_D18813'+label+'\n';(L/('PV_B3P_D188'+label+'13227.lean')).write_text(s)
# Exact file bytes are a prefix. Only harness fixture entrypoints follow.
rows=[]
for name in ['reference_terminal','reference_copy_terminal']:
 src=T/'v244'/(name+'.rs');data=src.read_bytes();(O/(name+'.rs')).write_bytes(data);rows.append(dict(file=name+'.rs',original_sha256=hashlib.sha256(data).hexdigest(),prefix_bytes=len(data)))
for name in ['host_terminal_constants.rs','host_copy_terminal_constants.rs']:shutil.copy2(T/'v244'/name,O/name)
with (O/'reference_terminal.rs').open('a')as f:f.write('''
pub fn observations13(seed:u32) {
 let n=(seed+1)*131; let state=core::array::from_fn(|i|crate::q13(n+i as u32));
 let mut packed=core::array::from_fn(|i|crate::q13(n+i as u32));let old=packed;
 add_preweighted(&mut packed,3,&core::array::from_fn::<_,7,_>(|i|crate::q13(seed+31+i as u32)));
 assert_ne!(packed,old);crate::emit13("add_preweighted",seed,&packed);
 let output=core::array::from_fn(|i|crate::q13(n+i as u32));
 let digest=add_digest_binding(output,crate::q13(seed+13),state,8,core::array::from_fn(|i|M31(seed+43+i as u32)),true);
 assert_ne!(digest,output);crate::emit13("add_digest_binding",seed,&digest);
}
''')
with (O/'reference_copy_terminal.rs').open('a')as f:f.write('''
pub fn observations13(seed:u32) {
 let n=(seed+1)*131;let state=core::array::from_fn(|i|crate::q13(n+i as u32));
 let values=pattern_values_literal(&state,crate::q13(seed+17));assert_ne!(values,[QM31::ZERO;14]);crate::emit13("pattern_values_literal",seed,&values);
 let selectors=Selectors{high:core::array::from_fn(|i|crate::q13(n+100+i as u32)),low:state};
 let active=selectors.active_literal();assert_ne!(active,QM31::ZERO);crate::emit13("active_literal",seed,&[active]);
}
''')
lib=(T/'v244/lib.rs').read_text()
for name in ['host_terminal_field','host_copy_terminal','host_terminal','reference_field','reference_poseidon','std194227']:
 lib=re.sub(r'(?m)^(pub )?mod '+name+r';',lambda m:'#[path="../v244/'+name+'.rs"] '+(m[1]or'')+'mod '+name+';',lib)
lib+='''
fn q13(n:u32)->aspis_core::field::QM31 { use aspis_core::field::{M31,CM31,QM31,P};QM31{c0:CM31::new(M31(n%P),M31(n.wrapping_mul(17)%P)),c1:CM31::new(M31(n.wrapping_mul(31)%P),M31(n.wrapping_mul(47)%P))}}
fn emit13(name:&str,seed:u32,values:&[aspis_core::field::QM31]) {
 let mut words:Vec<u32>=values.iter().flat_map(|x|[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]).collect();
 if std::env::args().any(|x|x=="--negative")&&name=="add_preweighted"&&seed==0 {words[0]^=1;}
 println!("{{\\"function\\":\\"{name}\\",\\"seed\\":{seed},\\"limbs\\":{words:?}}}");
}
pub fn d18813(){assert!(!cfg!(debug_assertions));for seed in [0,1,7,19] {reference_terminal::observations13(seed);reference_copy_terminal::observations13(seed);}}
''';(O/'lib.rs').write_text(lib);(O/'main.rs').write_text('fn main(){pv_b3p6_reference227::d18813();}\n')
cargo=(T/'v244-safe13/Cargo.toml').read_text();cargo=cargo[:cargo.index('[[bin]]')]+'''[[bin]]
name="d18813"
path="main.rs"
''';(O/'Cargo.toml').write_text(cargo);shutil.copy2(T/'v244-safe13/Cargo.lock',O/'Cargo.lock')
(D/'resume13/d188-fixture-source.json').write_text(json.dumps(dict(files=rows,scope='four new exact owned emission observation families, four canonical changed-output cases each; native equality finite only'),indent=2)+'\n')
