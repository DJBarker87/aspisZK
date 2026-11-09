//! AUDIT ONLY (`audit-eight-way`, PREREG-PROOF-SIZE-2 item 4): the retired
//! eight-way R1 verifier (per-query eight-way Merkle paths, 124,343-byte S2
//! proof), moved here unchanged from `verifier` when the compact
//! binary-multiproof format was adopted. It exists only for differential
//! evidence against saved eight-way fixtures; lib.rs makes it a compile error
//! together with `prover` or on an SBF target, and no default entrypoint
//! reaches it.
use super::*;

impl<'a> View<'a> {
    #[inline(never)]
    fn parse_shape(bytes:&'a[u8])->Result<Self,Error> {
        #[cfg(not(feature = "private-leaf-salts"))]
        let magic = b"R1P2COST";
        #[cfg(feature = "private-leaf-salts")]
        let magic = b"R1P3COST";
        if bytes.len()<HEADER||&bytes[..8]!=magic||bytes[9..16].iter().any(|&x|x!=0) {return Err(Error::Parse);}
        let v=Variant::from_tag(bytes[8]).ok_or(Error::Parse)?;
        if bytes.len()!=Self::eight_way_proof_bytes(v) {return Err(Error::Parse);}
        let mut at=HEADER;
        let semantic=&bytes[at..at+SEMANTIC_BYTES];at+=SEMANTIC_BYTES;
        let y1=&bytes[at..at+29*32];at+=29*32;
        let inactive=E::from_le_bytes(&bytes[at..at+32]).ok_or(Error::Parse)?;at+=32;
        let round0=&bytes[at..at+7*32];at+=7*32;
        let (folded_root,round1)=if v.folds()==2 {
            let root=bytes[at..at+32].try_into().unwrap();at+=32;
            let round=&bytes[at..at+7*32];at+=7*32;(Some(root),round)
        }else{(None,&[][..])};
        let final_message=&bytes[at..at+v.final_len()*32];at+=v.final_len()*32;
        let query_bytes=&bytes[at..];
        Ok(Self{variant:v,semantic,y1,inactive,round0,folded_root,round1,final_message,query_bytes})
    }
    #[inline(never)]
    pub fn parse(bytes:&'a[u8])->Result<Self,Error> {
        let out=Self::parse_shape(bytes)?;
        echeck(out.y1,true)?;
        echeck(out.round0,false)?;
        if let Some(round1)=out.folded_root.map(|_|out.round1) {echeck(round1,false)?;}
        echeck(out.final_message,false)?;
        for i in 0..22 {
            let q=out.query(i);
            for s in 0..4 {
                for l in 0..26 {M31::from_le_bytes(q[s*120+l*4..s*120+l*4+4].try_into().unwrap()).ok_or(Error::Parse)?;}
                K::from_le_bytes(&q[s*120+104..s*120+120]).ok_or(Error::Parse)?;
                for l in 0..2 {K::from_le_bytes(&q[480+s*32+l*16..480+s*32+l*16+16]).ok_or(Error::Parse)?;}
            }
            if out.variant.folds()==2 {echeck(&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128],false)?;}
        }
        Ok(out)
    }
    pub fn query(&self,i:usize)->&'a[u8] {let width=INITIAL_QUERY_BYTES+if self.variant.folds()==2 {SECOND_QUERY_BYTES}else{0};&self.query_bytes[i*width..(i+1)*width]}
}
fn merkle_path<H:Digest32>(hash:H,root:&[u8;32],mut index:usize,mut node:[u8;32],path:&[u8])->bool {
    for d in 0..6 {
        let slot=index%8;
        let children=core::array::from_fn(|s| {
            if s==slot {node}else{let j=s-usize::from(s>slot);path[d*224+j*32..d*224+j*32+32].try_into().unwrap()}
        });
        node=merkle::parent_with_digest(hash,&children);index/=8;
    }
    node==*root&&index==0
}
#[inline(never)]
pub fn query<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer)->Result<(),Error> {
    let geometry=QueryGeometry::for_range(&p.queries,a.next,a.next+1)?;
    query_with_geometry(v,p,a,g,hash,obs,&geometry,None)
}
#[inline(never)]
fn query_with_geometry<H:Digest32>(v:&View<'_>,p:&Prepared,a:&mut Accumulator,g:&[E;29],hash:H,obs:Observer,geometry:&QueryGeometry,pending:Option<&mut BatchedWeights>)->Result<(),Error> {
    let i=a.next;let u=p.queries[i] as usize;let q=v.query(i);
    #[cfg(not(feature = "private-leaf-salts"))]
    let (c1,c2,path_at) = (merkle::leaf_with_digest(hash,merkle::C1_TAG,&q[..480]),merkle::leaf_with_digest(hash,merkle::C2_TAG,&q[480..608]),608);
    #[cfg(feature = "private-leaf-salts")]
    let (c1,c2,path_at) = (
        aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,merkle::C1_TAG,&q[..480],q[608..640].try_into().unwrap()),
        aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,merkle::C2_TAG,&q[480..608],q[640..672].try_into().unwrap()),
        672,
    );
    if !merkle_path(hash,&p.roots[0],u,c1,&q[path_at..path_at+1344])||!merkle_path(hash,&p.roots[1],u,c2,&q[path_at+1344..INITIAL_QUERY_BYTES]) {return Err(Error::Merkle);}
    if p.variant.folds()==2 {
        let folded=&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128];
        #[cfg(not(feature = "private-leaf-salts"))]
        let (leaf,path_offset)=(merkle::leaf_with_digest(hash,0x72,folded),INITIAL_QUERY_BYTES+128);
        #[cfg(feature = "private-leaf-salts")]
        let (leaf,path_offset)=(
            aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(hash,0x72,folded,q[INITIAL_QUERY_BYTES+128..INITIAL_QUERY_BYTES+160].try_into().unwrap()),
            INITIAL_QUERY_BYTES+160,
        );
        if !merkle_path(hash,v.folded_root.unwrap(),u/4,leaf,&q[path_offset..]) {return Err(Error::Merkle);}
    }
    mark(obs,Phase::Merkle(i));
    let dots=crate::fast_dots::four_dots(q,g);#[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,0));for s in 0..4 {crate::trace::value(9,4*i+s,dots[s]);}
    let inverse=geometry.for_query(i);
    let mut folded=circle_fold_with_inverses(p.alpha[0],dots,inverse);crate::trace::value(10,2*i,folded);#[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,1));
    if p.variant.folds()==2 {
        let values=core::array::from_fn(|s|field(&q[INITIAL_QUERY_BYTES..],s));
        if folded!=values[u%4] {return Err(Error::Query);}
        folded=line_fold_with_inverses(p.alpha[1],values,inverse);crate::trace::value(10,2*i+1,folded);
    }
    #[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,2));
    let node=if p.variant.folds()==2 {
        let z=geometry.line_z[i-geometry.start];z.mul(z).double().sub(M31::ONE)
    } else {crate::fast_domain::line_node(domain::FibreIndex::new(u).unwrap())};
    accumulate_with_node(p,a,node,folded,pending);
    mark(obs,Phase::Query(i));Ok(())
}
#[inline(never)]
fn tx1_finish<H:Digest32>(v:View<'_>,p:Box<Prepared>,mut a:Accumulator,g:[E;29],public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    let geometry=QueryGeometry::for_range(&p.queries,0,k)?;
    let mut pending=BatchedWeights::new(&a.weights)?;
    while a.next<k {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry,Some(&mut pending))?;}
    pending.finish(&mut a.weights);
    let bytes=checkpoint(&p,&a,proof,public_bytes,hash);mark(obs,Phase::CheckpointWrite);Ok(bytes)
}

#[inline(never)]
fn tx1_prepare<H:Digest32>(public:Public<'_>,v:&View<'_>,hash:H,obs:Observer,g:&mut [E;29])->Result<(Box<[[K;29];3]>,Box<Prepared>),Error> {
    let sem=crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)?;mark(obs,Phase::Semantic);
    let p=Prepared::new(&sem,v,hash,g)?;
    Ok((sem.claims,p))
}

#[inline(never)]
pub fn tx1<H:Digest32>(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    if k>22 {return Err(Error::Parse);}
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let mut g=[E::ZERO;29];
    let (_semantic_claims,p)=tx1_prepare(public,&v,hash,obs,&mut g)?;let a=Accumulator::new(v.variant)?;mark(obs,Phase::Prepare);
    tx1_finish(v,p,a,g,public_bytes,proof,k,hash,obs)
}
/// Complete strict verification of an R1 proof and its checkpoint.
///
/// Runtime precondition: the checkpoint must be an authentic output of `tx1`
/// for the proof and public statement bound by its hashes. `resume` recomputes
/// both hashes from the current buffers: changes reject except for a collision.
/// The checkpoint checksum is an unkeyed hash, not a MAC, and
/// does not establish checkpoint provenance by itself. This strict entrypoint
/// repeats the full canonical scan of proof fields and query values.
#[inline(never)]
pub fn tx2<H:Digest32>(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,obs:Observer)->Result<(),Error> {
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let (p,mut a)=resume(checkpoint,proof,public_bytes,v.variant,hash)?;let g=powers::<29>(p.gamma);mark(obs,Phase::CheckpointRead);
    let geometry=QueryGeometry::for_range(&p.queries,a.next,22)?;
    let mut pending=BatchedWeights::new(&a.weights)?;
    while a.next<22 {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry,Some(&mut pending))?;}
    pending.finish(&mut a.weights);
    finish_relation(&v,&p,&a,obs)
}

/// Complete verification using proof bytes whose checkpoint provenance was
/// established by the caller.
///
/// Runtime precondition: the checkpoint must be an authentic output of `tx1`
/// for the proof and public statement bound by its hashes. This is also a
/// precondition of strict `tx2`. `resume` recomputes the proof/public hashes;
/// changed buffers reject except for a collision. The checkpoint checksum is
/// an unkeyed hash, not a MAC, and does not
/// establish checkpoint provenance by itself. This entrypoint only skips the
/// redundant per-field canonical scan of the proof; use strict `tx2` when that
/// scan is required.
#[inline(never)]
pub fn tx2_authenticated<H:Digest32>(public_bytes:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,obs:Observer)->Result<(),Error> {
    let v=View::parse_shape(proof)?;mark(obs,Phase::Parsed);
    let (p,mut a)=resume(checkpoint,proof,public_bytes,v.variant,hash)?;let g=powers::<29>(p.gamma);mark(obs,Phase::CheckpointRead);
    let geometry=QueryGeometry::for_range(&p.queries,a.next,22)?;
    let mut pending=BatchedWeights::new(&a.weights)?;
    while a.next<22 {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry,Some(&mut pending))?;}
    pending.finish(&mut a.weights);
    finish_relation(&v,&p,&a,obs)
}
