//! Exact bounded F31 causal geometry controls. Not a payment acceptance game.
//! All received words are fixed before alpha; no tau/provider input chooses Q.
use std::collections::BTreeSet;
const P:u32=31;
type Poly=[u32;4];
const POINTS:[(u32,u32);7]=[(2,11),(4,4),(5,10),(7,13),(10,5),(11,2),(13,7)];
fn add(a:u32,b:u32)->u32{(a+b)%P}
fn sub(a:u32,b:u32)->u32{(a+P-b)%P}
fn mul(a:u32,b:u32)->u32{a*b%P}
fn power(mut a:u32,mut n:u32)->u32{let mut out=1;while n!=0{if n&1==1{out=mul(out,a);}a=mul(a,a);n>>=1;}out}
fn inv(a:u32)->u32{assert_ne!(a,0);power(a,P-2)}
fn eval(p:&[u32],x:u32)->u32{p.iter().rev().fold(0,|a,c|add(mul(a,x),*c))}
fn product(roots:&[u32])->Vec<u32>{let mut p=vec![1];for r in roots{let mut q=vec![0;p.len()+1];for(i,c)in p.iter().enumerate(){q[i]=sub(q[i],mul(*r,*c));q[i+1]=add(q[i+1],*c);}p=q;}p}
fn slots((x,y):(u32,u32))->[(u32,u32);4]{[(x,y),(x,sub(0,y)),(sub(0,x),sub(0,y)),(sub(0,x),y)]}
fn encode(point:(u32,u32),p:Poly)->[u32;4]{slots(point).map(|(x,y)|add(add(p[0],mul(y,p[1])),add(mul(x,p[2]),mul(mul(x,y),p[3]))))}
fn fold((x,y):(u32,u32),w:[u32;4],a:u32)->u32{
 let left=add(mul(add(w[0],w[1]),inv(2)),mul(mul(a,sub(w[0],w[1])),inv(mul(2,y))));
 let right=sub(mul(add(w[2],w[3]),inv(2)),mul(mul(a,sub(w[2],w[3])),inv(mul(2,y))));
 add(mul(add(left,right),inv(2)),mul(mul(mul(a,a),sub(left,right)),inv(mul(2,x))))
}
fn interpolate(samples:&[(u32,u32)])->Poly{
 assert_eq!(samples.len(),4);let mut out=[0;4];
 for (i,(a,y)) in samples.iter().enumerate(){
  let others:Vec<u32>=samples.iter().enumerate().filter(|(j,_)|i!=*j).map(|(_,s)|s.0).collect();
  let p=product(&others);let denom=others.iter().fold(1,|d,b|mul(d,sub(*a,*b)));
  let scale=mul(*y,inv(denom));for j in 0..4{out[j]=add(out[j],mul(scale,p[j]));}
 }out
}
fn eligible(words:&[Poly],b:usize)->Vec<(u32,u32)>{
 let mut out=vec![];for a in 0..P{
  let mut counts=[0usize;P as usize];
  for(i,w)in words.iter().enumerate(){let value=fold(POINTS[i],encode(POINTS[i],*w),a);assert_eq!(value,eval(w,a));counts[value as usize]+=1;}
  // Enumerate every constant final AFTER this alpha, never after queries.
  for f in 0..P{if words.len()-counts[f as usize]<=b{out.push((a,f));}}
 }out
}
fn main(){
 let mut seen=BTreeSet::new();let mut finals=BTreeSet::new();
 for p in POINTS{assert_eq!(add(mul(p.0,p.0),mul(p.1,p.1)),1);assert_ne!(mul(p.0,p.1),0);
  for s in slots(p){assert!(seen.insert(s));}assert!(finals.insert(sub(mul(2,mul(p.0,p.0)),1)));}
 let nodes=[1,2,3,4];
 let prototypes:[Poly;7]=std::array::from_fn(|i|if i<4{
  product(&nodes.iter().copied().filter(|a|*a!=nodes[i]).collect::<Vec<_>>()).try_into().unwrap()
 }else{[(i+1)as u32,0,1,0]});
 let (mut sparse,mut dense,mut identified)=(0usize,0usize,0usize);
 let mut max_anchor_distance=0;
 for case in 0..3usize.pow(7){
  let mut digits=case;let words:[Poly;7]=std::array::from_fn(|i|{let s=(digits%3)as u32;digits/=3;prototypes[i].map(|x|mul(s,x))});
  let good=eligible(&words,1);
  assert_eq!(good.iter().map(|v|v.0).collect::<BTreeSet<_>>().len(),good.len());
  if good.len()<4{sparse+=1;continue;}
  dense+=1;
  let anchor=interpolate(&good[..4]);
  let distance=words.iter().enumerate().filter(|(i,w)|encode(POINTS[*i],**w)!=encode(POINTS[*i],anchor)).count();
  assert!(distance<=4);max_anchor_distance=max_anchor_distance.max(distance);
  for(a,final_value)in good{assert_eq!(eval(&anchor,a),final_value);identified+=1;}
 }
 assert_eq!(sparse+dense,2187);assert!(sparse>0&&dense>0);assert_eq!(max_anchor_distance,4);
 // Strict-gap falsifier: T=5, B=1, cap=0 gives T-5B=0, not >0.
 // The five cubics h(X)-prod_{j!=i}(X-a_j), h=X^4, have one error
 // each at five near-final values h(a_i). No cubic can cover all five.
 let five=[1,2,3,4,5];let mut boundary=vec![];
 for i in 0..5{let roots:Vec<u32>=five.iter().copied().filter(|a|*a!=five[i]).collect();let p=product(&roots);
  assert_eq!(p[4],1);boundary.push(std::array::from_fn(|j|sub(0,p[j])));}
 let good=eligible(&boundary,1);assert_eq!(good.len(),5);
 for(a,f)in &good{assert_eq!(*f,power(*a,4));}
 let anchor=interpolate(&good[..4]);assert_ne!(eval(&anchor,good[4].0),good[4].1);
 // Four accepted alpha values cannot force a degree-six relation error
 // to be identically zero: this degree-four error has nonzero boundary.
 let discrepancy=product(&nodes);let prior=mul(4,add(discrepancy[0],discrepancy[4]));assert_eq!(prior,7);
 let sent=[discrepancy[0],discrepancy[1],discrepancy[2],discrepancy[3],0,0];
 let rebuilt=[sent[0],sent[1],sent[2],sent[3],sub(mul(prior,inv(4)),sent[0]),sent[4],sent[5]];
 for a in 0..P{assert_eq!(eval(&rebuilt,a),eval(&discrepancy,a));}
 assert_eq!((0..P).filter(|a|eval(&rebuilt,*a)==0).collect::<Vec<_>>(),nodes);
 println!(r#"{{"field":31,"received_family_cases":2187,"sparse_cases":{},"dense_cases":{},"covered_near_finals":{},"maximum_anchor_distance":{},"all_alpha_final_pairs_per_word":961,"strict_gap_counterexample":{{"T":5,"B":1,"overlap_cap":0,"eligible_alphas":5,"coverage_fails":true}},"compact_four_root_control":{{"degree":4,"boundary":7,"roots":4}},"received_fixed_before_alpha":true,"anchor_uses_tau_or_provider":false,"scope":"exhaustive ternary received family and all adaptive constant-code finals; not full strategy, payment or QM31 security"}}"#,sparse,dense,identified,max_anchor_distance);
}
