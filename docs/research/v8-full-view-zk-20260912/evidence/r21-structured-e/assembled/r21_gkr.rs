//! R21 bounded GKR arithmetic pilot. Not an Aspis acceptance path.
//! No claim of Fiat--Shamir soundness: the shared-oracle proof remains open.
//! Fixed circuit wiring is compiled into the executable, never prover supplied.
use aspis_core::field::{QM31 as K,CM31,M31,P};
#[cfg(not(target_os="solana"))]
use sha2::{Digest,Sha256};
fn hash(parts:&[&[u8]])->[u8;32]{
    #[cfg(target_os="solana")] {solana_program::hash::hashv(parts).to_bytes()}
    #[cfg(not(target_os="solana"))] {let mut h=Sha256::new();for p in parts{h.update(p);}h.finalize().into()}
}

#[derive(Clone,Copy,Debug)]
pub struct Gate(pub u8,pub u16,pub u16); // add,mul,sub,copy,zero
#[derive(Clone,Copy)]
pub enum Input { Public(u8), Constant([u32;4]) }
pub struct Circuit {
    pub id:[u8;32], pub inputs:&'static[Input], pub layers:&'static[&'static[Gate]],
}
pub fn integer(x:u32)->K {K{c0:CM31::new(M31(x),M31::ZERO),c1:CM31::ZERO}}
pub fn bits(n:usize)->usize {n.next_power_of_two().trailing_zeros() as usize}
fn eval_gate(g:Gate,a:K,b:K)->K {match g.0 {0=>a.add(b),1=>a.mul(b),2=>a.sub(b),3=>a,4=>K::ZERO,_=>panic!("static circuit opcode")}}
fn eval_poly(p:&[K],x:K)->K {p.iter().rev().fold(K::ZERO,|s,&v|s.mul(x).add(v))}
fn encoded(v:K)->[u8;16]{let mut b=[0;16];v.write_le_bytes(&mut b);b}
pub fn input_values(c:&Circuit,p:&[K;24])->Vec<K> {
    c.inputs.iter().map(|v|match v {Input::Public(i)=>p[*i as usize],Input::Constant(q)=>{
        assert!(q.iter().all(|&x|x<P));K{c0:CM31::new(M31(q[0]),M31(q[1])),c1:CM31::new(M31(q[2]),M31(q[3]))}
    }}).collect()
}
pub fn evaluate(c:&Circuit,p:&[K;24])->Vec<Vec<K>> {
    let mut levels=vec![input_values(c,p)];
    for layer in c.layers {
        let prev=levels.last().unwrap();
        levels.push(layer.iter().map(|&g|eval_gate(g,prev[g.1 as usize],prev[g.2 as usize])).collect());
    }
    levels
}
fn fold(v:&mut Vec<K>,x:K) {
    for i in 0..v.len()/2 {let a=v[2*i];v[i]=a.add(x.mul(v[2*i+1].sub(a)));}
    v.truncate(v.len()/2);
}
fn multilinear(v:&[K],z:&[K])->K {
    let mut work=v.to_vec();work.resize(1<<z.len(),K::ZERO);
    for &x in z {fold(&mut work,x);} work[0]
}
fn equality_table(z:&[K],out:&mut[K]) {
    assert!(out.len()>=1<<z.len());out[0]=K::ONE;
    let mut n=1;
    for &x in z {
        for j in 0..n {let v=out[j];out[j+n]=v.mul(x);out[j]=v.sub(out[j+n]);}
        n*=2;
    }
}

struct Transcript([u8;32]);
impl Transcript {
    fn new(c:&Circuit,context:&[u8;32],inputs:&[K;24],output:K)->Result<Self,()> {
        let mut data=[0u8;400];
        for (i,v) in inputs.iter().chain(core::iter::once(&output)).enumerate() {
            let bytes=encoded(*v);if K::from_le_bytes(&bytes)!=Some(*v){return Err(());}
            data[16*i..16*i+16].copy_from_slice(&bytes);
        }
        Ok(Self(hash(&[b"Aspis/R21/public-arithmetic/GKR-pilot/v1",&c.id,context,&data])))
    }
    fn absorb(&mut self,label:u8,values:&[K]) {
        assert!(values.len()<=32);
        let mut data=[0u8;512];for(i,&v)in values.iter().enumerate(){data[16*i..16*i+16].copy_from_slice(&encoded(v));}
        self.0=hash(&[&self.0,&[label],&(values.len() as u32).to_le_bytes(),&data[..16*values.len()]]);
    }
    fn challenge(&mut self)->Result<K,()> {
        // An explicit pilot sampler; no IID/shared-oracle security inference.
        for ctr in 0..16u32 {
            let d=hash(&[&self.0,b"challenge",&ctr.to_le_bytes()]);let limbs:[u32;4]=core::array::from_fn(|i|u32::from_le_bytes(d[4*i..4*i+4].try_into().unwrap())&P);
            if limbs.iter().all(|&x|x<P) {
                let x=K{c0:CM31::new(M31(limbs[0]),M31(limbs[1])),c1:CM31::new(M31(limbs[2]),M31(limbs[3]))};
                self.absorb(255,&[x]);return Ok(x);
            }
        }Err(())
    }
}
struct Reader<'a>{b:&'a[u8],at:usize}
impl Reader<'_>{fn field(&mut self)->Result<K,()>{let b=self.b.get(self.at..self.at+16).ok_or(())?;let v=K::from_le_bytes(b).ok_or(())?;self.at+=16;Ok(v)}}
fn push(b:&mut Vec<u8>,v:K){b.extend_from_slice(&encoded(v));}
pub fn proof_fields(c:&Circuit)->usize {
    let mut n=0;let mut prev=c.inputs.len();
    for layer in c.layers {let k=bits(prev);n+=4*k+2+k+1;prev=layer.len();}n
}

/// Complete verifier for the fixed *arithmetic relation*, including input MLE
/// and all wiring. It is not the full original verifier or a security theorem.
#[inline(never)]
pub fn verify(c:&Circuit,context:&[u8;32],inputs:&[K;24],output:K,proof:&[u8])->Result<(),()> {
    if c.id!=[6, 12, 210, 70, 221, 241, 157, 87, 152, 193, 142, 198, 16, 49, 107, 28, 142, 225, 139, 146, 39, 215, 31, 83, 164, 23, 93, 199, 240, 76, 224, 61]{return Err(());}
    if c.layers.last().map(|x|x.len())!=Some(1) || proof.len()!=16*proof_fields(c){return Err(());}
    let mut tr=Transcript::new(c,context,inputs,output)?;
    let mut rd=Reader{b:proof,at:0};let mut claim=output;let mut z=Vec::new();
    let max_width=c.layers.iter().map(|l|l.len()).chain(core::iter::once(c.inputs.len())).max().unwrap().next_power_of_two();
    // Reuse three buffers; no per-layer heap growth in the SBF bump allocator.
    let mut scratch=vec![K::ZERO;(3*max_width).max(r21_wiring::MAX_NODES)];
    let max_bits=bits(max_width);let mut u=vec![K::ZERO;max_bits];let mut v=u.clone();
    let mut line=vec![K::ZERO;max_bits+1];
    for level in (0..c.layers.len()).rev() {
        let layer=c.layers[level];let prev_len=if level==0{c.inputs.len()}else{c.layers[level-1].len()};let k=bits(prev_len);
        for round in 0..2*k {
            let c0=rd.field()?;let c2=rd.field()?;let c1=claim.sub(c0.add(c0)).sub(c2);
            tr.absorb(1,&[c0,c2]);let r=tr.challenge()?;
            claim=c0.add(r.mul(c1.add(r.mul(c2))));
            if round<k{u[round]=r}else{v[round-k]=r}
        }
        let vu=rd.field()?;let vv=rd.field()?;tr.absorb(2,&[vu,vv]);
        if claim!=r21_wiring::endpoint(level,&z,&u[..k],&v[..k],vu,vv,&mut scratch){return Err(());}
        for value in &mut line[..=k]{*value=rd.field()?;}
        if line[0]!=vu || line[..=k].iter().copied().fold(K::ZERO,K::add)!=vv{return Err(());}
        tr.absorb(3,&line[..=k]);let r=tr.challenge()?;claim=eval_poly(&line[..=k],r);
        z.resize(k,K::ZERO);for i in 0..k{z[i]=u[i].add(r.mul(v[i].sub(u[i])));}
    }
    let ez=&mut scratch[..max_width];equality_table(&z,ez);
    // Evaluate ALL public inputs and fixed constants, not a prover claim.
    let mut actual=K::ZERO;
    for (i,item) in c.inputs.iter().enumerate(){let x=match item{Input::Public(j)=>inputs[*j as usize],Input::Constant(a)=>K{c0:CM31::new(M31(a[0]),M31(a[1])),c1:CM31::new(M31(a[2]),M31(a[3]))}};actual=actual.add(ez[i].mul(x));}
    if rd.at!=proof.len() || actual!=claim{return Err(());}Ok(())
}

fn line_polynomial(values:&[K],u:&[K],v:&[K])->Vec<K> {
    let n=1<<u.len();let mut ps:Vec<Vec<K>>=(0..n).map(|i|vec![values.get(i).copied().unwrap_or(K::ZERO)]).collect();
    for r in 0..u.len() {
        let d=v[r].sub(u[r]);let mut next=Vec::with_capacity(ps.len()/2);
        for pair in ps.chunks_exact(2){let mut p=vec![K::ZERO;r+2];for j in 0..=r{let diff=pair[1][j].sub(pair[0][j]);p[j]=p[j].add(pair[0][j]).add(u[r].mul(diff));p[j+1]=p[j+1].add(d.mul(diff));}next.push(p);}ps=next;
    }ps.pop().unwrap()
}

/// Honest public-data-only prover. No witness or mask-seed argument exists.
pub fn prove(c:&Circuit,context:&[u8;32],inputs:&[K;24])->Result<(K,Vec<u8>),()> {
    let levels=evaluate(c,inputs);let output=levels.last().ok_or(())?[0];
    let mut tr=Transcript::new(c,context,inputs,output)?;let mut proof=Vec::new();let mut z=Vec::new();let mut claim=output;
    for level in (0..c.layers.len()).rev() {
        let layer=c.layers[level];let values=&levels[level];let k=bits(values.len());
        let mut ez=vec![K::ZERO;1<<z.len()];equality_table(&z,&mut ez);
        let mut gate_weight=ez[..layer.len()].to_vec();
        let mut work=values.clone();work.resize(1<<k,K::ZERO);
        let mut u=Vec::new();let mut v=Vec::new();let mut vu=K::ZERO;
        for round in 0..2*k {
            let t=round%k;if round==k{work=values.clone();work.resize(1<<k,K::ZERO);vu=multilinear(values,&u);}
            let mut ys=[K::ZERO;3];
            for (g,&gate) in layer.iter().enumerate(){
                if gate.0==4{continue;}
                let index=if round<k{gate.1 as usize}else{gate.2 as usize};let slot=index>>(t+1);
                let a=work[2*slot];let d=work[2*slot+1].sub(a);
                for x in 0..3 {let xk=integer(x as u32);let value=a.add(d.mul(xk));
                    let eq=if (index>>t)&1==1{xk}else{K::ONE.sub(xk)};
                    let term=if round<k{eval_gate(gate,value,values[gate.2 as usize])}else{eval_gate(gate,vu,value)};
                    ys[x]=ys[x].add(gate_weight[g].mul(eq).mul(term));
                }
            }
            assert_eq!(ys[0].add(ys[1]),claim,"sumcheck honest layer {level} round {round}");
            let c0=ys[0];let c2=ys[2].sub(ys[1].add(ys[1])).add(ys[0]).half();let c1=claim.sub(c0.add(c0)).sub(c2);
            push(&mut proof,c0);push(&mut proof,c2);tr.absorb(1,&[c0,c2]);let r=tr.challenge()?;
            claim=c0.add(r.mul(c1.add(r.mul(c2))));
            for (g,&gate) in layer.iter().enumerate(){let index=if round<k{gate.1 as usize}else{gate.2 as usize};let eq=if(index>>t)&1==1{r}else{K::ONE.sub(r)};gate_weight[g]=gate_weight[g].mul(eq);}
            fold(&mut work,r);if round<k{u.push(r)}else{v.push(r)}
        }
        // k=0 works too: both endpoints are the single input value.
        vu=multilinear(values,&u);let vv=multilinear(values,&v);push(&mut proof,vu);push(&mut proof,vv);tr.absorb(2,&[vu,vv]);
        let p=line_polynomial(values,&u,&v);for &a in &p{push(&mut proof,a);}tr.absorb(3,&p);let r=tr.challenge()?;
        claim=eval_poly(&p,r);z=u.iter().zip(&v).map(|(&a,&b)|a.add(r.mul(b.sub(a)))).collect();
    }
    assert_eq!(proof.len(),16*proof_fields(c));Ok((output,proof))
}

#[cfg(not(target_os="solana"))]
pub fn verify_reference(c:&Circuit,context:&[u8;32],inputs:&[K;24],output:K,proof:&[u8])->Result<(),()> {
    if c.layers.last().map(|x|x.len())!=Some(1) || proof.len()!=16*proof_fields(c){return Err(());}
    let mut tr=Transcript::new(c,context,inputs,output)?;
    let mut rd=Reader{b:proof,at:0};let mut claim=output;let mut z=Vec::new();
    let max_width=c.layers.iter().map(|l|l.len()).chain(core::iter::once(c.inputs.len())).max().unwrap().next_power_of_two();
    // Reuse three buffers; no per-layer heap growth in the SBF bump allocator.
    let mut scratch=vec![K::ZERO;3*max_width];
    let max_bits=bits(max_width);let mut u=vec![K::ZERO;max_bits];let mut v=u.clone();
    let mut line=vec![K::ZERO;max_bits+1];
    for level in (0..c.layers.len()).rev() {
        let layer=c.layers[level];let prev_len=if level==0{c.inputs.len()}else{c.layers[level-1].len()};let k=bits(prev_len);
        for round in 0..2*k {
            let c0=rd.field()?;let c2=rd.field()?;let c1=claim.sub(c0.add(c0)).sub(c2);
            tr.absorb(1,&[c0,c2]);let r=tr.challenge()?;
            claim=c0.add(r.mul(c1.add(r.mul(c2))));
            if round<k{u[round]=r}else{v[round-k]=r}
        }
        let vu=rd.field()?;let vv=rd.field()?;tr.absorb(2,&[vu,vv]);
        let (ez,rest)=scratch.split_at_mut(max_width);let (eu,ev)=rest.split_at_mut(max_width);
        equality_table(&z,ez);equality_table(&u[..k],eu);equality_table(&v[..k],ev);
        let mut left=K::ZERO;let mut right=K::ZERO;let mut product=K::ZERO;
        for (g,&gate) in layer.iter().enumerate() {
            if gate.0==4{continue;}
            let weight=ez[g].mul(eu[gate.1 as usize]).mul(ev[gate.2 as usize]);
            match gate.0 {0=>{left=left.add(weight);right=right.add(weight)},1=>product=product.add(weight),2=>{left=left.add(weight);right=right.sub(weight)},3=>left=left.add(weight),_=>return Err(())}
        }
        if claim!=left.mul(vu).add(right.mul(vv)).add(product.mul(vu).mul(vv)){return Err(());}
        for value in &mut line[..=k]{*value=rd.field()?;}
        if line[0]!=vu || line[..=k].iter().copied().fold(K::ZERO,K::add)!=vv{return Err(());}
        tr.absorb(3,&line[..=k]);let r=tr.challenge()?;claim=eval_poly(&line[..=k],r);
        z.resize(k,K::ZERO);for i in 0..k{z[i]=u[i].add(r.mul(v[i].sub(u[i])));}
    }
    let ez=&mut scratch[..max_width];equality_table(&z,ez);
    // Evaluate ALL public inputs and fixed constants, not a prover claim.
    let mut actual=K::ZERO;
    for (i,item) in c.inputs.iter().enumerate(){let x=match item{Input::Public(j)=>inputs[*j as usize],Input::Constant(a)=>K{c0:CM31::new(M31(a[0]),M31(a[1])),c1:CM31::new(M31(a[2]),M31(a[3]))}};actual=actual.add(ez[i].mul(x));}
    if rd.at!=proof.len() || actual!=claim{return Err(());}Ok(())
}


#[path="r21_wiring.rs"] pub mod r21_wiring;
