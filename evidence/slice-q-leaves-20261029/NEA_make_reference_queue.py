from pathlib import Path
import json
E=Path(__file__).resolve().parent
prefix='''extern crate alloc;
use alloc::vec::Vec;
pub trait Ops {fn mul(a:u32,b:u32)->u32;}
pub fn prefix_ref<O:Ops>(flat:&[u32])->(Vec<u32>,u32){let mut out=Vec::with_capacity(flat.len());let mut p=1;let mut i=0;while i<flat.len(){let v=flat[i];out.push(p);p=O::mul(p,v);i+=1;}(out,p)}
pub fn prefix_step_ref<O:Ops>(mut out:Vec<u32>,p:u32,v:u32,i:usize)->(Vec<u32>,u32,usize){out.push(p);let next=O::mul(p,v);(out,next,i+1)}
'''
geo='''extern crate alloc;
use alloc::vec::Vec;
pub trait Ops {fn point(u:usize)->(u32,u32);fn line(u:usize)->u32;fn mul(a:u32,b:u32)->u32;fn double(a:u32)->u32;fn sub(a:u32,b:u32)->u32;fn inv(a:u32)->u32;}
pub struct Geometry {pub start:usize,pub inverses:Vec<[u32;5]>,pub line_z:Vec<u32>}
fn index_ref(u:usize)->Result<usize,u8>{if u<262144{Ok(u)}else{Err(1)}}
pub fn geometry_step_ref<O:Ops>(q:u32)->Result<([u32;5],u32),u8>{let u=q as usize;let f=index_ref(u)?;let (x,y)=O::point(f);let lx=O::line(index_ref(u/4*4)?);let ly=O::line(index_ref(u/4*4+3)?);let square=O::mul(lx,lx);let twice=O::double(square);let z=O::sub(twice,1);let v=[x,y,lx,ly,z];for x in v{if x==0{return Err(1);}}Ok((v,z))}
pub fn geometry_ref<O:Ops>(queries:&[u32;22],start:usize,end:usize)->Result<Geometry,u8>{if start>end||end>22{return Err(1);}let mut zs=Vec::with_capacity(end-start);let mut flat=Vec::with_capacity((end-start)*5);for &q in &queries[start..end]{let(v,z)=geometry_step_ref::<O>(q)?;flat.extend_from_slice(&v);zs.push(z);}if flat.is_empty(){return Ok(Geometry{start,inverses:Vec::new(),line_z:zs});}let mut prefixes=Vec::with_capacity(flat.len());let mut p=1;let mut i=0;while i<flat.len(){prefixes.push(p);p=O::mul(p,flat[i]);i+=1;}let mut suffix=O::inv(p);let mut inv=Vec::with_capacity(flat.len());inv.resize(flat.len(),0);for j in (0..flat.len()).rev(){inv[j]=O::mul(suffix,prefixes[j]);suffix=O::mul(suffix,flat[j]);}let mut groups=Vec::with_capacity(zs.len());for k in 0..zs.len(){groups.push([inv[5*k],inv[5*k+1],inv[5*k+2],inv[5*k+3],inv[5*k+4]]);}Ok(Geometry{start,inverses:groups,line_z:zs})}
pub fn geometry_append_ref<O:Ops>(mut flat:Vec<u32>,mut zs:Vec<u32>,q:u32)->Result<(Vec<u32>,Vec<u32>),u8>{let(v,z)=geometry_step_ref::<O>(q)?;flat.extend_from_slice(&v);zs.push(z);Ok((flat,zs))}
'''
row='''extern crate alloc;
use alloc::vec::Vec;
pub fn row_ref(mut row:[u64;4],power:[u32;4],basis:u32,flush:bool)->[u64;4]{for j in 0..4{let old=row[j];let limb=power[j];row[j]=old+u64::from(limb)*u64::from(basis);}if flush{for limb in &mut row{*limb=(*limb&2147483647)+(*limb>>31);}}row}
pub struct Weights {pub raw:Vec<[u64;4]>,pub terms:usize}
pub fn push_ref(mut w:Weights,index:usize,power:[u32;4],basis:u32)->Weights{let flush=w.terms&3==3;w.raw[index]=row_ref(w.raw[index],power,basis,flush);w}
pub fn row_add_limb_ref(mut row:[u64;4],power:[u32;4],basis:u32,j:usize)->[u64;4]{let old=row[j];row[j]=old+u64::from(power[j])*u64::from(basis);row}
pub fn row_fold_limb_ref(mut row:[u64;4],j:usize)->[u64;4]{let old=row[j];row[j]=(old&2147483647)+(old>>31);row}
'''
dots='''pub trait Ops<E,T>{fn limbs(x:E)->[u32;8];fn from_limbs(x:[u32;8])->Option<E>;fn reduce(x:u64)->u32;fn parse_k(b:&[u8])->Option<[u32;4]>;fn tail_new()->T;fn tail_push(t:T,x:E,k:[u32;4])->Result<T,u8>;fn tail_finish(t:T)->E;fn add(x:E,y:E)->E;}
fn read_m(b:&[u8])->u32{let x=u32::from_le_bytes([b[0],b[1],b[2],b[3]]);assert!(x<2147483647);x}
pub fn dot_term_ref<E:Copy,T,O:Ops<E,T>>(q:&[u8;608],g:&[E;29],slot:usize,term:usize,mut sums:[u64;8])->[u64;8]{let at=slot*120+term*4;let scalar=read_m(&q[at..at+4]);let c=O::limbs(g[term]);for j in 0..8{sums[j]+=u64::from(c[j])*u64::from(scalar);}sums}
pub fn dots_one_ref<E:Copy,T,O:Ops<E,T>>(q:&[u8;608],g:&[E;29],slot:usize)->E{let mut limbs=[0u64;8];let mut start=0;while start<26{let mut sums=[0u64;8];let stop=core::cmp::min(start+4,26);for term in start..stop{sums=dot_term_ref::<E,T,O>(q,g,slot,term,sums);}for j in 0..8{limbs[j]+=(sums[j]&2147483647)+(sums[j]>>31);}start+=4;}let v=O::from_limbs([O::reduce(limbs[0]),O::reduce(limbs[1]),O::reduce(limbs[2]),O::reduce(limbs[3]),O::reduce(limbs[4]),O::reduce(limbs[5]),O::reduce(limbs[6]),O::reduce(limbs[7])]).unwrap();let mut tail=O::tail_new();let k=O::parse_k(&q[slot*120+104..slot*120+120]).unwrap();tail=O::tail_push(tail,g[28],k).ok().unwrap();let at=480+slot*32;let k=O::parse_k(&q[at..at+16]).unwrap();tail=O::tail_push(tail,g[26],k).ok().unwrap();let k=O::parse_k(&q[at+16..at+32]).unwrap();tail=O::tail_push(tail,g[27],k).ok().unwrap();O::add(v,O::tail_finish(tail))}
'''
four='''pub trait Ops<E>{fn one(q:&[u8;608],g:&[E;29],slot:usize)->E;}
pub fn four_ref<E,O:Ops<E>>(q:&[u8],g:&[E;29])->[E;4]{let q:&[u8;608]=q[..608].try_into().unwrap();[O::one(q,g,0),O::one(q,g,1),O::one(q,g,2),O::one(q,g,3)]}
'''
cm='''pub trait Ops{fn mul(x:u32,y:u32)->u32;fn add(x:u32,y:u32)->u32;fn neg(x:u32)->u32;fn inv(x:u32)->u32;}
pub fn cm_inv_ref<O:Ops>(x:[u32;2])->[u32;2]{let aa=O::mul(x[0],x[0]);let bb=O::mul(x[1],x[1]);let norm=O::add(aa,bb);let n=O::inv(norm);[O::mul(x[0],n),O::mul(O::neg(x[1]),n)]}
pub fn cm_inv_with_ref<O:Ops>(x:[u32;2],inverse:fn(u32)->u32)->[u32;2]{let aa=O::mul(x[0],x[0]);let bb=O::mul(x[1],x[1]);let norm=O::add(aa,bb);let n=inverse(norm);[O::mul(x[0],n),O::mul(O::neg(x[1]),n)]}
'''
qm='''pub trait Ops{fn square(x:[u32;2])->[u32;2];fn sub(x:[u32;2],y:[u32;2])->[u32;2];fn by_r(x:[u32;2])->[u32;2];fn inv(x:[u32;2])->[u32;2];fn mul(x:[u32;2],y:[u32;2])->[u32;2];fn neg(x:[u32;2])->[u32;2];}
pub fn qm_try_ref<O:Ops>(x:[u32;4])->Option<[u32;4]>{if x==[0;4]{return None;}let a=[x[0],x[1]];let b=[x[2],x[3]];let aa=O::square(a);let bb=O::square(b);let norm=O::sub(aa,O::by_r(bb));let n=O::inv(norm);let lo=O::mul(a,n);let hi=O::mul(O::neg(b),n);Some([lo[0],lo[1],hi[0],hi[1]])}
'''
qwrap='''pub trait Ops{fn try_inv(x:[u32;4])->Option<[u32;4]>;}
pub fn qm_inv_ref<O:Ops>(x:[u32;4])->[u32;4]{O::try_inv(x).expect("cannot invert zero in QM31")}
'''
acc='''extern crate alloc;
use alloc::vec::Vec;
pub trait Ops<E,K>{fn m_mul(a:u32,b:u32)->u32;fn m_double(a:u32)->u32;fn m_sub(a:u32,b:u32)->u32;fn push(w:Vec<[u64;4]>,index:usize,power:K,basis:u32,flush:bool)->Vec<[u64;4]>;fn e_add(a:E,b:E)->E;fn e_mul_k(a:E,b:K)->E;fn k_mul(a:K,b:K)->K;}
pub struct State<E,K>{pub weights:Vec<K>,pub rhs:E,pub power:K,pub next:usize}
pub struct Pending{pub raw:Vec<[u64;4]>,pub terms:usize}
pub fn accumulate_ref<E:Copy,K:Copy,O:Ops<E,K>>(mut a:State<E,K>,mut w:Pending,rho:K,mut node:u32,value:E)->(State<E,K>,Pending){let width=a.weights.len();let mut basis=[0u32;256];basis[0]=1;let mut n=1;while n<width{for j in 0..n{basis[n+j]=O::m_mul(basis[j],node);}node=O::m_sub(O::m_double(O::m_mul(node,node)),1);n*=2;}for j in 0..width{w.raw=O::push(w.raw,j,a.power,basis[j],w.terms&3==3);}w.terms+=1;a.rhs=O::e_add(a.rhs,O::e_mul_k(value,a.power));a.power=O::k_mul(a.power,rho);a.next+=1;(a,w)}
'''
# Trace is a no-op in the deployed non-prover build. This reference does not invent an Observer.
fold=(E/'NEA_fold_reference.rs.txt').read_text()
fold+='''
pub fn horner_step_ref<E:Copy,M:Copy,O:NEA_Ops<E,M>>(alpha:E,coefficient:E,rest:E)->E{let product=O::mul(alpha,rest);O::add(coefficient,product)}
pub fn circle_h0_ref<E:Copy,M:Copy,O:NEA_Ops<E,M>>(a:[E;4],quarter:M)->E{let ab=O::add(a[0],a[1]);let abc=O::add(ab,a[2]);let abcd=O::add(abc,a[3]);O::scale(abcd,quarter)}
pub fn circle_h3_ref<E:Copy,M:Copy,O:NEA_Ops<E,M>>(a:[E;4],ix:M,iy:M,quarter:M)->E{let ab=O::sub(a[0],a[1]);let abc=O::add(ab,a[2]);let abcd=O::sub(abc,a[3]);let m=O::base_mul(quarter,ix);let m1=O::base_mul(m,iy);O::scale(abcd,m1)}
'''
items=[
 ('Prefix',prefix,['prefix_ref'],'batch_prefix_products'),
 ('Geometry',geo,['geometry_ref'],'QueryGeometry::for_range'),
 ('Residue',row,['row_ref'],'update_residue_row'),
 ('Weights',row,['push_ref'],'BatchedWeights::push'),
 ('DotsOne',dots,['dots_one_ref'],'four_dots_one'),
 ('FourDots',four,['four_ref'],'four_dots'),
 ('CMInverse',cm,['cm_inv_ref'],'CM31::inv'),
 ('CMBackend',cm,['cm_inv_with_ref'],'CM31::inv_with'),
 ('QMTry',qm,['qm_try_ref'],'QM31::try_inv; explicit CM31::square outside-slice boundary'),
 ('QMInverse',qwrap,['qm_inv_ref'],'QM31::inv'),
 ('Accumulate',acc,['accumulate_ref'],'accumulate_batched_with_node; deployed trace is no-op'),
 ('FoldCuts',fold,['horner_step_ref','circle_h0_ref','circle_h3_ref'],'circle/line fold split candidates; not full native credit'),
 ('PrefixStep',prefix,['prefix_step_ref'],'batch_prefix_products arbitrary-prestate iteration'),
 ('DotRowWindows',dots+'\n'+row,['dot_term_ref','row_add_limb_ref','row_fold_limb_ref'],'four_dots_one/update_residue_row per-limb windows')]
queue=[]
for k,(label,source,roots,member) in enumerate(items,7):
 name='NEA_'+label+'_reference.rs.txt';(E/name).write_text(source)
 queue.append(dict(attempt=f'NEA_E{k:03d}',reference=name,namespace='NEA_'+label+'Ref',roots=['crate::'+r for r in roots],member=member,adoption='UNVALIDATED reference-only continuation; no Lean budget remains; no local/composed credit'))
(E/'NEA_REFERENCE_QUEUE.json').write_text(json.dumps(queue,indent=2)+'\n')
print('Prepared',len(queue),'member/window references; no claims promoted')
