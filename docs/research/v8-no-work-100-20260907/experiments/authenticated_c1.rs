//! Extractor-side API receives only an expected root and authenticated records.
//! No witness, message coefficients, masks or honest-anchor argument.
use super::*;
use super::circle_candidate::CircleEncoder;
use aspis_statement::state_only_trace::StateOnlyTraceFoundation;
pub const OPEN_FIBRES:usize=256;
#[derive(Clone)]
pub struct C1Openings {pub ids:Vec<u32>,pub leaves:Vec<Vec<u8>>,pub salts:Vec<[u8;32]>,pub frontier:Vec<u8>}
pub fn read31(b:&[u8],bit:usize)->Result<M31,Error>{
    let mut v=0;for j in 0..31{v|=(((b[(bit+j)/8]>>((bit+j)%8))&1)as u32)<<j;}
    if v>=corelib::field::P {Err(Error::Canonical)}else{Ok(M31(v))}
}
pub fn put31(b:&mut[u8],bit:usize,x:M31){assert!(x.0<corelib::field::P);
    for j in 0..31 {b[(bit+j)/8]|=(((x.0>>j)&1)as u8)<<((bit+j)%8);}
}
pub fn authenticate(root:[u8;26],o:&C1Openings)->Result<Vec<Vec<M31>>,Error>{
    if o.ids!=(0..256).collect::<Vec<u32>>()||o.leaves.len()!=256||o.salts.len()!=256{return Err(Error::Shape)}
    let mut entries=Vec::new();let mut values=vec![vec![M31::ZERO;1024];16];
    for i in 0..256{
        if o.leaves[i].len()!=403{return Err(Error::Length)}
        for slot in 0..4{for col in 0..26{
            let v=read31(&o.leaves[i],31*(slot*26+col))?;
            if col<16{values[col][4*i+slot]=v;}
        }}
        let leaf=private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&o.leaves[i],&o.salts[i]);
        entries.push((o.ids[i],leaf,leaf));
    }
    // Reuse the exact selected checker twice on the SAME C1 tree. This is
    // not a C2 authentication claim. Frontier bytes are supplied once and
    // borrowed twice; duplicated hash work is extractor work.
    if !verify_two_minimal_subtrees_v7_bytes(hash,(&root,&root),18,&entries,
        (&o.frontier,&o.frontier),&mut vec![],&mut vec![]){return Err(Error::Authentication)}
    Ok(values)
}
pub struct Decoder {inv:Vec<Vec<M31>>,pub pivots:usize}
impl Decoder {
    pub fn new(enc:&CircleEncoder)->Self{
        // Public fixed generator matrix for the source's EXACT message basis.
        let n=1024;let mut a=vec![vec![M31::ZERO;2*n];n];
        for i in 0..n{for j in 0..n{a[i][j]=enc.encode_c1_basis_value(j,i).unwrap();}a[i][n+i]=M31::ONE;}
        let mut pivots=0;
        for j in 0..n{
            let pivot=(j..n).find(|&i|a[i][j]!=M31::ZERO).expect("generator rank deficiency");
            a.swap(j,pivot);let inverse=a[j][j].inv();
            for k in j..2*n{a[j][k]=a[j][k].mul(inverse);}
            let (left,right)=a.split_at_mut(j);let (pivotrow,tail)=right.split_first_mut().unwrap();
            for row in left.iter_mut().chain(tail){let scale=row[j];if scale==M31::ZERO{continue}
                for k in j..2*n{row[k]=row[k].sub(scale.mul(pivotrow[k]));}}
            pivots+=1;
        }
        for i in 0..n{for j in 0..n{assert_eq!(a[i][j],if i==j{M31::ONE}else{M31::ZERO});}}
        Self{inv:a.into_iter().map(|r|r[n..].to_vec()).collect(),pivots}
    }
    pub fn solve_base(&self,values:&[M31])->Vec<M31>{assert_eq!(values.len(),1024);
        self.inv.iter().map(|r|r.iter().zip(values).fold(M31::ZERO,|s,(a,b)|s.add(a.mul(*b)))).collect()}
    pub fn solve_wide(&self,values:&[K])->Vec<K>{assert_eq!(values.len(),1024);
        self.inv.iter().map(|r|r.iter().zip(values).fold(K::ZERO,|s,(a,b)|s.add(b.mul_m31(*a)))).collect()}
}
pub fn recover_c1(root:[u8;26],o:&C1Openings,d:&Decoder)->Result<StateOnlyTraceFoundation,Error>{
    let values=authenticate(root,o)?;
    Ok(StateOnlyTraceFoundation{c1:std::array::from_fn(|col|d.solve_base(&values[col]))})
}
