from pathlib import Path
import re,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit21-20261021')
p=H/'src/crates/aspis-r1-cost-probe/src/transcript.rs';s=p.read_text();assert 'mod control21' not in s
body=s[s.index('pub struct Transcript'):s.index('#[cfg(kani)]')]
body=body.replace('Transcript<H: Digest32>', 'Transcript<H: Digest32,P:Policy>')
body=body.replace('impl<H: Digest32> Transcript<H>', 'impl<H: Digest32,P:Policy> Transcript<H,P>')
body=body.replace('pub state:[u8;32], hash:H','pub state:[u8;32], hash:H, pub trace:alloc::vec::Vec<(u16,usize,E)>, marker:core::marker::PhantomData<P>')
body=body.replace('semantic_state]), hash }','semantic_state]), hash, trace:alloc::vec::Vec::new(), marker:core::marker::PhantomData }')
body=body.replace('crate::sampler::gamma_sample','P::gamma').replace('crate::sampler::ordinary_sample','P::ordinary').replace('crate::sampler::qm31_sample','P::qm31')
body=body.replace('crate::trace::value(4,row as usize,out)','self.trace.push((4,row as usize,out))').replace('crate::trace::value(4,row as usize,E::from_qm31(out))','self.trace.push((4,row as usize,E::from_qm31(out)))')
body,n=re.subn(r'crate::trace::value\(5,(\d+),E::from_m31\(aspis_core::field::M31\(u\)\)\)',r'self.trace.push((5,\1,E::from_m31(aspis_core::field::M31(u))))',body);assert n==22
old='aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances).map_err(|_|crate::verifier::Error::Transcript)?'
assert old in body
body=body.replace(old,'match P::queries(&blocks,&advances) {Ok(v)=>v,Err(e)=>return Err(e)}')
trait='''pub trait Policy {
 fn gamma(block:&[u8;32])->E;
 fn ordinary(block:&[u8;32])->E;
 fn qm31(block:&[u8;32])->aspis_core::field::QM31;
 fn queries(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),crate::verifier::Error>;
}
'''
addition='\n#[cfg(any(kani,aeneas_ref))]\npub mod control21 {\nuse super::*;\n'+trait+body+'\n}\n'
p.unlink();p.write_text(s+addition);(H/'harness/transcript-control21.rs').write_text(addition)
p=H/'src/crates/aspis-r1-cost-probe/src/sim.rs';s=p.read_text();root=(H/'harness/tail21.rs').read_text().replace('tail_owned21<H:Digest32>','tail_control21<H:Digest32,P:crate::transcript::control21::Policy>').replace('z:[SecureCirclePoint;2]','z:[[K;2];2]').replace('Vec<(u16,usize,[u8;32])>','Vec<(u16,usize,E)>').replace('Result<Drawn,Error>','Result<([K;25],[[K;2];2],E,E,E,E,[u32;22],K),Error>').replace('crate::transcript::owned21::Transcript::new','crate::transcript::control21::Transcript::<H,P>::new').replace('Ok(Drawn{sem,z,gamma,kappa,alpha0,alpha1,queries,rho})','Ok((sem,z,gamma,kappa,alpha0,alpha1,queries,rho))')
p.unlink();p.write_text(s+'\n'+root);(H/'harness/tail-control21.rs').write_text(root)
(H/'control21-binding.json').write_text(json.dumps(dict(reference_sha256=hashlib.sha256(addition.encode()).hexdigest(),tail_sha256=hashlib.sha256(root.encode()).hexdigest(),scope='Generic policy callbacks and owned field-valued trace; actual source samplers and TLS identification remain explicit obligations'),indent=2)+'\n')
