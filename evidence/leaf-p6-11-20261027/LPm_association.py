"""Pin exact frozen checkpoint partitions; does not certify a whole native run."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent
R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
p='crates/aspis-r1-cost-probe/src/verifier.rs'
s=subprocess.check_output(['git','show',R+':'+p]).decode()
start=s.index('pub fn checkpoint<');end=s.index('\nstruct Reader',start)
body=s[start:end]
expected='''pub fn checkpoint<H:Digest32>(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],hash:H)->Vec<u8> {
    let mut out=Vec::with_capacity(checkpoint_size(p.variant));
    out.extend_from_slice(b"R1P2CKP2");out.extend_from_slice(&[p.variant.tag(),a.next as u8,1,0,0,0,0,0]);
    out.extend_from_slice(&hash.digest(&[proof]));out.extend_from_slice(&hash.digest(&[public]));out.extend_from_slice(&p.state);
    for root in &p.roots {out.extend_from_slice(root);}
    for x in [p.gamma,p.kappa,p.alpha[0],p.alpha[1]] {put(&mut out,x);}
    put_k(&mut out,p.rho);
    for q in p.queries {out.extend_from_slice(&q.to_le_bytes());}
    for x in p.semantic_alpha {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}
    for z in p.z {for x in [z.x,z.y] {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}}
    for x in [p.claim,a.rhs] {put(&mut out,x);}
    put_k(&mut out,a.power);
    for &x in &a.weights {put_k(&mut out,x);}
    let sum=hash.digest(&[b"UNPROVED:R1:checkpoint",&out]);out.extend_from_slice(&sum);
    assert_eq!(out.len(),checkpoint_size(p.variant));out
}'''
assert body==expected
rows=[('header',16,'LPe_K015'),('proof digest',32,'LPi_K018'),('public digest',32,'LPi_K018'),('p.state',32,'LPe_K016'),('p.roots',64,'LPe_K017'),('gamma,kappa,alpha[0],alpha[1]',128,'LPi_K013'),('p.rho',16,'LPi_K012'),('p.queries',88,'LPe_K017'),('p.semantic_alpha',160,'LPe_K019'),('p.z x,y',64,'LPe_K019'),('p.claim,a.rhs',64,'LPi_K013'),('a.power',16,'LPi_K012'),('a.weights',1024,'LPm_K001 + split continuation')]
blocks=[];at=0
for label,n,g in rows:blocks.append(dict(field=label,start=at,bytes=n,gate=g));at+=n
assert at==1736
assert body.count('hash.digest')==3
hashes={}
for f in ['evidence/leaf-p6-5-20261027/LPe_harness.patch','evidence/leaf-p6-6-20261027/LPf_harness.patch','evidence/leaf-p6-9-20261027/LPi_harness.patch','evidence/leaf-p6-9-20261027/LPi_REUSE.md']:
 b=Path(f).read_bytes();hashes[f]=dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
out=dict(frozen_revision=R,source=p,source_sha256=hashlib.sha256(s.encode()).hexdigest(),checkpoint_sha256=hashlib.sha256(body.encode()).hexdigest(),exact_source_partitions=True,source_line=s[:start].count('\n')+1,blocks=blocks,body_bytes=at,result_bytes=at+32,digest_order=['proof','physical public','label ++ SAME body'],inherited_packets=hashes,claim='Static source partition and inherited evidence pins only; not a whole native execution proof')
(E/'LPm_ASSOCIATION.json').write_text(json.dumps(out,indent=2)+'\n')
print('Exact frozen checkpoint body; 13 ordered partitions; 1736 body / 1768 result bytes')
