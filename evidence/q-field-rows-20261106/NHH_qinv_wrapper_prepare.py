from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;x=json.loads((E/'NHH_QINVERSE_INPUTS.json').read_text())
src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],text=True)
m=re.search(r'pub fn inv\(self\) -> QM31',src);a=src.index('{',m.end());i=a+1;d=1
while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[a+1:i-1];inst=body.replace('self.try_inv()','NHH_qsome(log,input)');assert inst.replace('NHH_qsome(log,input)','self.try_inv()')==body
extra='''
fn NHH_qsome(log:&mut Option<(QM31,QM31)>,input:QM31)->Option<QM31>{
 assert!(NHH_Ccanon(input.c0)&&NHH_Ccanon(input.c1)&&!input.is_zero());
 let a:[u32;4]=kani::any();kani::assume(a[0]<P&&a[1]<P&&a[2]<P&&a[3]<P);
 let out=QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}};
 *log=Some((input,out));Some(out)
}
fn NHH_inv_wrapper(log:&mut Option<(QM31,QM31)>,input:QM31)->QM31{
'''+inst+'''
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn qm_inv_log(){
 let a:[u32;4]=kani::any();kani::assume(a[0]<P&&a[1]<P&&a[2]<P&&a[3]<P&&(a[0]!=0||a[1]!=0||a[2]!=0||a[3]!=0));
 let input=QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}};
 let mut log=None;let out=NHH_inv_wrapper(&mut log,input);
 check(log==Some((input,out)));
}
'''
x['crates/aspis-r1-cost-probe/src/NHH_fields.rs']+=extra
(E/'NHH_fields_qinverse.rs.txt').write_text(x['crates/aspis-r1-cost-probe/src/NHH_fields.rs'])
(E/'NHH_QINVERSE_INPUTS.json').write_text(json.dumps(x));(E/'NHH_QINVERSE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()},indent=1)+'\n')
(E/'NHH_QWRAPPER_ERASURE.json').write_text(json.dumps(dict(function='QM31::inv',frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),instrumented_body_sha256=hashlib.sha256(inst.encode()).hexdigest(),erasure_equal=True,nonzero_reply='explicit Some canonical record from the same nonzero receiver; paired with source totality; full None/expect path separately checked',no_function_pointer_or_static=True),indent=1)+'\n')
