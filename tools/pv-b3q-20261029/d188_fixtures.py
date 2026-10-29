from pathlib import Path
import json,hashlib,re,shutil
D=Path('evidence/pv-b3q-20261029');T=Path('tools/pv-b3q-20261029/d188');T.mkdir(exist_ok=True);B=Path('tools/pv-b3p6-20261028/v244')
q=lambda n:'{ c0 := { a := '+str(n)+'#u32, b := '+str(n*17)+'#u32 }, c1 := { a := '+str(n*31)+'#u32, b := '+str(n*47)+'#u32 } }'
a=lambda n,base:'(Array.make '+str(n)+'#usize ['+', '.join(q(base+i)for i in range(n))+'] (by rfl))'
u=lambda n,base,ty:'(Array.make '+str(n)+'#usize ['+', '.join(str(base+i)+'#'+ty for i in range(n))+'] (by rfl))'
funcs=['absorption_lanes_literal','path_lanes_literal','add_value_lanes','occupancy_lanes_literal','external_linear_packed','internal_sum227','leading_pair_packed','interpolate_three_constant_columns','expand','accumulate_endpoint']
mods=[]
for ix,name in enumerate(funcs):
 m='PV_B3Q_D188Fixture'+str(ix);mods.append(m);s='''import PV_B3P_P227_14
namespace '''+m+'''
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def report {n : Usize} (r : Result (Array aspis_core.field.QM31 n)) : String :=
 match r with
 | .ok xs => reprStr (xs.val.flatMap (fun q => [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]))
 | .fail _ => "FAIL"
 | .div => "DIV"
'''
 for seed in [0,1,7,19]:
  n=(seed+1)*131;state=a(16,n);opening='{ z := '+state+', succ_z := '+a(16,n+20)+', xor12_z := '+a(16,n+40)+' }';selectors='{ high := '+a(64,n+100)+', low := '+state+' }'
  if name=='absorption_lanes_literal':expr='reference_terminal.'+name+' '+' '.join('('+q(seed+x)+')'for x in [11,13,17,19,23])+' '+state
  elif name=='path_lanes_literal':expr='reference_terminal.'+name+' ('+q(seed+37)+') ('+opening+')'
  elif name=='add_value_lanes':expr='reference_terminal.'+name+' '+a(24,n)+' ('+opening+') ('+selectors+')'
  elif name=='occupancy_lanes_literal':expr='reference_terminal.'+name+' ('+q(seed+41)+') ('+q(seed+43)+') '+str(seed+5)+'#u32 '+state
  elif name=='external_linear_packed':expr='reference_poseidon.'+name+' '+state
  elif name=='internal_sum227':
   s+='def sum'+str(seed)+' := reference_poseidon.internal_sum227 '+u(4,seed+17,'u64')+' ('+q(seed+53)+')\n'
   s+='#eval "'+name+':'+str(seed)+'=" ++ (match sum'+str(seed)+' with | .ok xs => reprStr (xs.val.map (fun x => x.val)) | .fail _ => "FAIL" | .div => "DIV")\n';continue
  elif name=='leading_pair_packed':expr='reference_poseidon.'+name+' ('+opening+')'
  elif name=='interpolate_three_constant_columns':expr='reference_poseidon.'+name+' '+a(3,seed+61)+' '+' '.join(u(16,seed+x,'u32')for x in [67,71,73])
  elif name=='expand':expr='reference_copy_terminal.Selectors.expand 16#usize '+a(10,seed+79)+' 0#usize 4#usize'
  else:expr='(do let (v,w) ← reference_copy_terminal.accumulate_endpoint '+a(2,n)+' '+a(2,n+2)+' { row := 19#u16, slot := 1#u8, pattern := 3#u8 } 17#u32 23#u32 '+a(14,n+4)+' ('+selectors+'); .ok (Array.make 4#usize (v.val ++ w.val) (by simp only [List.length_append,v.property,w.property]; rfl)))'
  s+='#eval "'+name+':'+str(seed)+'=" ++ report ('+expr+')\n'
 s+='end '+m+'\n';(D/'lean'/(m+'.lean')).write_text(s)
# Every source file stays an unchanged prefix, then native-only observation roots.
inputs={}
for name in ['reference_terminal','reference_copy_terminal','reference_poseidon']:
 raw=(B/(name+'.rs')).read_bytes();(T/(name+'.rs')).write_bytes(raw);inputs[name]=dict(prefix_bytes=len(raw),prefix_sha256=hashlib.sha256(raw).hexdigest())
for name in ['host_terminal_constants.rs','host_copy_terminal_constants.rs']:(T/name).write_bytes((B/name).read_bytes())
with(T/'reference_terminal.rs').open('a')as f:f.write('''
pub fn observe(seed:u32){
 let n=(seed+1)*131;let state=core::array::from_fn(|i|crate::q(n+i as u32));
 let openings=crate::openings(n);let selectors=crate::selectors(n);
 let out=absorption_lanes_literal(crate::q(seed+11),crate::q(seed+13),crate::q(seed+17),crate::q(seed+19),crate::q(seed+23),&state);
 assert_ne!(out,[QM31::ZERO;16]);crate::emit("absorption_lanes_literal",seed,&out);
 let out=path_lanes_literal(crate::q(seed+37),&openings);assert_ne!(out,[QM31::ZERO;17]);crate::emit("path_lanes_literal",seed,&out);
 let mut packed=core::array::from_fn(|i|crate::q(n+i as u32));let before=packed;add_value_lanes(&mut packed,&openings,&selectors);assert_ne!(packed,before);crate::emit("add_value_lanes",seed,&packed);
 let out=occupancy_lanes_literal(crate::q(seed+41),crate::q(seed+43),M31(seed+5),&state);assert_ne!(out,[QM31::ZERO;12]);crate::emit("occupancy_lanes_literal",seed,&out);
}
''')
with(T/'reference_poseidon.rs').open('a')as f:f.write('''
pub fn observe(seed:u32){
 let n=(seed+1)*131;let state=core::array::from_fn(|i|crate::q(n+i as u32));
 let out=external_linear_packed(state);assert_ne!(out,[QM31::ZERO;4]);crate::emit("external_linear_packed",seed,&out);
 let initial=core::array::from_fn(|i|(seed+17+i as u32)as u64);let out=internal_sum227(initial,crate::q(seed+53));assert_ne!(out,initial);crate::emit_words("internal_sum227",seed,&out);
 let out=leading_pair_packed(&crate::openings(n));assert_ne!(out,[QM31::ZERO;4]);crate::emit("leading_pair_packed",seed,&out);
 let weights=core::array::from_fn(|i|crate::q(seed+61+i as u32));let c0=core::array::from_fn(|i|seed+67+i as u32);let c1=core::array::from_fn(|i|seed+71+i as u32);let c2=core::array::from_fn(|i|seed+73+i as u32);
 let out=interpolate_three_constant_columns(weights,c0,c1,c2);assert_ne!(out,[QM31::ZERO;16]);crate::emit("interpolate_three_constant_columns",seed,&out);
}
''')
with(T/'reference_copy_terminal.rs').open('a')as f:f.write('''
pub fn observe(seed:u32){
 let n=(seed+1)*131;let point=core::array::from_fn(|i|crate::q(seed+79+i as u32));let out=Selectors::expand::<16>(&point,0,4);assert_ne!(out,[QM31::ZERO;16]);crate::emit("expand",seed,&out);
 let mut values=core::array::from_fn(|i|crate::q(n+i as u32));let mut weights=core::array::from_fn(|i|crate::q(n+2+i as u32));let oldv=values;let oldw=weights;
 accumulate_endpoint(&mut values,&mut weights,CompiledPoolV1PairForestEndpoint{row:19,slot:1,pattern:3},17,M31(23),&core::array::from_fn(|i|crate::q(n+4+i as u32)),&crate::selectors(n));
 assert_ne!(values,oldv);assert_ne!(weights,oldw);crate::emit("accumulate_endpoint",seed,&[values[0],values[1],weights[0],weights[1]]);
}
''')
(D/'d188-fixtures.json').write_text(json.dumps(dict(modules=mods,functions=funcs,inputs=inputs,evidence_class='finite validation of owned source vs exact emitted model; no changed-function native association'),indent=2)+'\n')
