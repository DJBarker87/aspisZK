from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
n='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
s=subprocess.check_output(['git','show','4bb3b3f5:'+n],text=True)
body=s.split('fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {',1)[1].split('\n}',1)[0]
repls=[('chi.sub(row.producer_values[0])','op(chi,row.producer_values[0],o[0],0,0,l)'),('chi.sub(row.producer_values[1])','op(chi,row.producer_values[1],o[1],1,0,l)'),('chi.sub(row.consumer_values[0])','op(chi,row.consumer_values[0],o[2],2,0,l)'),('chi.sub(row.consumer_values[1])','op(chi,row.consumer_values[1],o[3],3,0,l)'),('denominators[0].mul(denominators[1])','op(denominators[0],denominators[1],o[4],4,1,l)'),('denominators[2].mul(denominators[3])','op(denominators[2],denominators[3],o[5],5,1,l)'),('row.producer_weights[0]\n        .mul(denominators[1])\n        .add(row.producer_weights[1].mul(denominators[0]))','op(op(row.producer_weights[0],denominators[1],o[6],6,1,l),op(row.producer_weights[1],denominators[0],o[7],7,1,l),o[8],8,2,l)'),('row.consumer_weights[0]\n        .mul(denominators[3])\n        .add(row.consumer_weights[1].mul(denominators[2]))','op(op(row.consumer_weights[0],denominators[3],o[9],9,1,l),op(row.consumer_weights[1],denominators[2],o[10],10,1,l),o[11],11,2,l)'),('producer_denominator\n        .mul(helper.mul(consumer_denominator).add(consumer_numerator))\n        .sub(consumer_denominator.mul(producer_numerator))','op(op(producer_denominator,op(op(helper,consumer_denominator,o[12],12,1,l),consumer_numerator,o[13],13,2,l),o[14],14,1,l),op(consumer_denominator,producer_numerator,o[15],15,1,l),o[16],16,0,l)')]
cut=body
for a,b in repls:assert cut.count(a)==1;cut=cut.replace(a,b)
module='''
#[cfg(kani)]
mod NIX_residual {
 use super::*;
 fn q()->QM31 {kani::any()}
 fn same(a:QM31,b:QM31)->bool {a.c0.a.0==b.c0.a.0&&a.c0.b.0==b.c0.b.0&&a.c1.a.0==b.c1.a.0&&a.c1.b.0==b.c1.b.0}
 fn canonical(a:QM31)->bool {a.c0.a.0<aspis_core::field::P&&a.c0.b.0<aspis_core::field::P&&a.c1.a.0<aspis_core::field::P&&a.c1.b.0<aspis_core::field::P}
 struct Log {args:[QM31;34],kind:[u8;17],at:[u8;17],count:u8,frame:u64}
 fn op(a:QM31,b:QM31,value:QM31,i:usize,kind:u8,l:&mut Log)->QM31 {l.args[2*i]=a;l.args[2*i+1]=b;l.kind[i]=kind;l.at[i]=l.count;l.count+=1;value}
 fn step(row:CopyRowExtension,helper:QM31,chi:QM31,o:[QM31;17],l:&mut Log)->QM31 {BODY
 }
 fn check(negative:bool){
  let row=CopyRowExtension{producer_values:[q(),q()],producer_weights:[q(),q()],consumer_values:[q(),q()],consumer_weights:[q(),q()]};let helper=q();let chi=q();
  for a in [row.producer_values[0],row.producer_values[1],row.producer_weights[0],row.producer_weights[1],row.consumer_values[0],row.consumer_values[1],row.consumer_weights[0],row.consumer_weights[1],helper,chi]{kani::assume(canonical(a));}
  let o=[OUTPUTS];for a in o {kani::assume(canonical(a));}
  let count:u8=kani::any();kani::assume(count<239);let frame:u64=kani::any();let mut l=Log{args:[ARGS],kind:kani::any(),at:kani::any(),count,frame};
  let mut result=step(row,helper,chi,o,&mut l);if negative{result.c0.a.0^=1;}
  let expected=[(chi,row.producer_values[0]),(chi,row.producer_values[1]),(chi,row.consumer_values[0]),(chi,row.consumer_values[1]),(o[0],o[1]),(o[2],o[3]),(row.producer_weights[0],o[1]),(row.producer_weights[1],o[0]),(o[6],o[7]),(row.consumer_weights[0],o[3]),(row.consumer_weights[1],o[2]),(o[9],o[10]),(helper,o[5]),(o[12],o[11]),(o[4],o[13]),(o[5],o[8]),(o[14],o[15])];
  let i:usize=kani::any();kani::assume(i<17);assert!(same(l.args[2*i],expected[i].0)&&same(l.args[2*i+1],expected[i].1));assert!(canonical(l.args[2*i])&&canonical(l.args[2*i+1]));let kinds=[0u8,0,0,0,1,1,1,1,2,1,1,2,1,2,1,1,0];assert_eq!(l.kind[i],kinds[i]);assert_eq!(l.at[i],count+i as u8);assert_eq!(l.count,count+17);assert_eq!(l.frame,frame);assert!(same(result,o[16]));
 }
 #[kani::proof] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn native(){check(false);}
 #[kani::proof] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn control(){check(true);}
}
'''.replace('BODY',cut).replace('OUTPUTS',','.join(['q()']*17)).replace('ARGS',','.join(['q()']*34))
(E/'NIX_residual.rs.txt').write_text(module)
(E/'NIX_RESIDUAL_REPLACEMENTS.json').write_text(json.dumps(repls,indent=2)+'\n')
p=E/'NIX_src'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s+module)
nlib='crates/aspis-statement/src/lib.rs';lib=subprocess.check_output(['git','show','4bb3b3f5:'+nlib],text=True)
lib='#![cfg_attr(kani, feature(allocator_api))]\n'+lib+'\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NIX_kmx;\n';p=E/'NIX_src'/nlib;p.write_text(lib)
pins=json.loads((E/'NIX_SOURCE_PINS.json').read_text())
for name in [n,nlib]:pins[name]=hashlib.sha256((E/'NIX_src'/name).read_bytes()).hexdigest()
(E/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins))
(E/'NIX_RESIDUAL_ERASURE.json').write_text(json.dumps(dict(frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),cut_body_sha256=hashlib.sha256(cut.encode()).hexdigest(),substitutions=17,ordered_local_log=True,field_arithmetic_executed=False),indent=2)+'\n')
x=json.loads((E/'NIX_L055.json').read_text());x.update(attempt='NIX_L056',module='Install exact residual17 local-record cut',sources=['NIX_src/'+n,'NIX_src/'+nlib,'NIX_SOURCE_PINS.json','NIX_RESIDUAL_ERASURE.json'],command=['python3','-c','import json;print(json.load(open("NIX_RESIDUAL_ERASURE.json")))']);(E/'NIX_L056.json').write_text(json.dumps(x,indent=2))
