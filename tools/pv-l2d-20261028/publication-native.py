"""Exact publication_indices body and finite output/control instrumentation."""
from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
p=R/'crates/aspis-r1-cost-probe/src/prover.rs';s=p.read_text();a=s.index('fn publication_indices(');b=s.index('\nfn publish_compact',a);body=s[a:b].strip()
expected='''fn publication_indices(queries:&[u32;22],begin:usize,end:usize,folded:bool)->Vec<u32> {
    let mut out=Vec::with_capacity(end-begin);
    let mut i=begin;
    while i<end {
        let value=if folded {queries[i]/4} else {queries[i]};
        let mut at=0;
        while at<out.len() && out[at]<value {at+=1;}
        if at==out.len() || out[at]!=value {out.insert(at,value);}
        i+=1;
    }
    out
}'''
flat=lambda s:re.sub(r'\s+','',s)
assert flat(body)==flat(expected),'review changed body; no silent template refresh'
ins=body.replace('fn publication_indices','fn instrumented',1).replace('->Vec<u32>','->(Vec<u32>,Vec<(u8,usize)>)',1)
ins=ins.replace('let mut out=','let mut trace=vec![];let mut out=',1)
changes=[('i<end','obs(0,i<end,&mut trace)'),('if folded','if obs(1,folded,&mut trace)'),('queries[i]','queries[ix(2,i,&mut trace)]'),('at<out.len()','obs(3,at<out.len(),&mut trace)'),('out[at]<value','obs(4,out[ix(5,at,&mut trace)]<value,&mut trace)'),('at==out.len()','obs(6,at==out.len(),&mut trace)'),('out[at]!=value','obs(7,out[ix(8,at,&mut trace)]!=value,&mut trace)'),('out.insert(at,value)','out.insert(ix(9,at,&mut trace),value)')]
for x,y in changes:
 assert x in ins,x
 ins=ins.replace(x,y)
ins=ins[:-len('out\n}')]+ '(out,trace)\n}'
# Reverse these literal observer insertions to check that all original tokens
# and the short-circuit && / || evaluation order survive.
back=ins
for x,y in reversed(changes):back=back.replace(y,x)
back=back.replace('let mut trace=vec![];','').replace('fn instrumented','fn publication_indices',1).replace('->(Vec<u32>,Vec<(u8,usize)>)','->Vec<u32>',1)
back=back.replace('(out,trace)\n}','out\n}')
assert flat(back)==flat(body)
raw=body+'\n'+r'''
fn obs(tag:u8,b:bool,t:&mut Vec<(u8,usize)>)->bool {t.push((tag,b as usize));b}
fn ix(tag:u8,i:usize,t:&mut Vec<(u8,usize)>)->usize {t.push((tag,i));i}
'''+ins+r'''
fn check(q:&[u32;22],begin:usize,end:usize,folded:bool)->usize {
 let native=publication_indices(q,begin,end,folded);
 let (value,trace)=instrumented(q,begin,end,folded);assert_eq!(native,value);
 let mut expected:Vec<u32>=q[begin..end].iter().map(|&x|if folded {x/4} else {x}).collect();
 expected.sort();expected.dedup();assert_eq!(native,expected);
 assert!(trace.iter().filter(|(tag,_)|[2,5,8,9].contains(tag)).all(|(_,i)|*i<=22));
 1
}
fn main(){
 let mut checks=0;let mut state=0x5a5a_1234_5678_9abcu64;
 for case in 0..256 {
  let q=std::array::from_fn(|i|match case {
   0=>0,1=>i as u32,2=>(21-i) as u32,3=>(i%4) as u32,
   _=>{state^=state<<13;state^=state>>7;state^=state<<17;(state as u32)&((1<<18)-1)}
  });
  for begin in 0..=22 {for end in begin..=22 {for folded in [false,true] {checks+=check(&q,begin,end,folded);}}}
 }
 let q=std::array::from_fn(|i|i as u32);let reversed=std::array::from_fn(|i|(21-i) as u32);
 assert_eq!(publication_indices(&q,0,22,false),publication_indices(&reversed,0,22,false));
 assert_ne!(instrumented(&q,0,22,false).1,instrumented(&reversed,0,22,false).1);
 println!("{{\"checks\":{},\"same_set_different_control\":true,\"failed\":0}}",checks);
}
'''
out=R/'tools/pv-l2d-20261028/publication-native.rs';out.write_text(raw)
(E/'publication-native-freeze.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),instrumentation_erases_exactly=True,observer_identities='obs returns its Bool argument; ix returns its usize argument; both only append to a separate trace',short_circuit_order_preserved=True,evidence_class='exact body freeze + finite validation preparation; no whole-row/native universal claim',harness_sha256=hashlib.sha256(raw.encode()).hexdigest()),indent=2)+'\n')
print('publication body and erasing control instrumentation frozen')
