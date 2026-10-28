from pathlib import Path
import subprocess,difflib,os
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 out={}
 def base(n):return subprocess.check_output(['git','show',REV+':'+n],text=True)
 # Only cfg(kani) attributes/modules in scratch frozen files.
 for root in ['crates/aspis-r1-cost-probe','programs/r1-cost-probe','crates/aspis-core','crates/aspis-statement']:
  n=root+'/src/lib.rs';b=base(n)
  out[n]='#![cfg_attr(kani, feature(allocator_api))]\n'+b+'\n#[cfg(kani)]\nmod NDH_kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n'
  out[n]+='\n#[cfg(kani)]\n#[path="NDH_reference.rs"]\nmod NDH_reference;\n'
 spec=[('crates/aspis-r1-cost-probe/src/fast_domain.rs','table','fn table_value(value: (u32, u32)) -> CM31','(r.a.0,r.b.0) == NDH_native::reference::table_ref(value)'),('crates/aspis-r1-cost-probe/src/compact.rs','slot','pub const fn slot_offset(slot: usize) -> usize','*r == NDH_native::reference::slot_ref(slot)')]
 for n,tag,sig,prop in spec:
  b=base(n);s=b.replace(sig,f'#[cfg_attr(kani,kani::ensures(|r| ({prop}) != cfg!(NDH_invert_{tag})))]\n'+sig,1)
  s+='\n#[cfg(kani)]\n#[path="NDH_'+tag+'.rs"]\nmod NDH_native;\n';out[n]=s
  out[str(Path(n).parent/('NDH_'+tag+'.rs'))]=(E/('NDH_'+tag+'.rs.txt')).read_text()
 # Root-owned public helper tests are added only to the verifier's root.
 n='crates/aspis-r1-cost-probe/src/lib.rs';out[n]+='\n#[cfg(kani)]\n#[path="NDH_public.rs"]\nmod NDH_public;\n'
 out['crates/aspis-r1-cost-probe/src/NDH_public.rs']=(E/'NDH_public.rs.txt').read_text()
 for root in ['crates/aspis-r1-cost-probe','programs/r1-cost-probe','crates/aspis-core','crates/aspis-statement']:
  out[root+'/src/NDH_reference.rs']=(E/'NDH_reference.rs.txt').read_text()
 # Contracts on real frozen dependency helpers, cfg-only, no body edit.
 n='crates/aspis-core/src/r0/domain.rs';b=base(n)
 b=b.replace('            pub const fn get(self)', '#[cfg_attr(kani,kani::ensures(|r| (*r == self.0) != cfg!(NDH_invert_get)))]\n            pub const fn get(self)')
 b=b.replace('            pub fn new(index:', '#[cfg_attr(kani,kani::ensures(|r| (match r {Ok(v)=>v.0==index && index < $bound,Err(Error::IndexOutOfRange)=>index >= $bound,_=>false}) != cfg!(NDH_invert_new)))]\n            pub fn new(index:')
 out[n]=b
 n='crates/aspis-statement/src/pool_v1/verifier_registry.rs';b=base(n)
 for name,prop in [('is_paused','crate::NDH_reference::flag_ref(self.flags,1)'),('is_immutable','crate::NDH_reference::flag_ref(self.flags,2)'),('has_no_retirement_slot','crate::NDH_reference::retirement_ref(self.retirement_slot)')]:
  b=b.replace('    pub fn '+name+'(',f'    #[cfg_attr(kani,kani::ensures(|r| (*r == ({prop})) != cfg!(NDH_invert_{name}))) ]\n    pub fn '+name+'(')
 b=b.replace('fn required_binding_is_zero(', '#[cfg_attr(kani,kani::ensures(|r| (*r == value.iter().all(|b| *b==0)) != cfg!(NDH_invert_binding)))]\nfn required_binding_is_zero(')
 out[n]=b
 n='crates/aspis-core/src/r0_transcript.rs';b=base(n)
 prop='match (r,crate::NDH_reference::finish_ref(self.accepted,self.accepted_len)) {(Ok(a),Ok(b))=>crate::NDH_reference::eq22(a,&b),(Err(QuerySampleError::DrawLimitExhausted{accepted,max_draws}),Err((a,b)))=>*accepted==a && *max_draws==b,_=>false}'
 b=b.replace('    fn finish(self)',f'    #[cfg_attr(kani,kani::ensures(|r| ({prop}) != cfg!(NDH_invert_finish)))]\n    fn finish(self)')
 b+='\n#[cfg(kani)]\n#[path="NDH_coretranscript.rs"]\nmod NDH_native;\n';out[n]=b
 out['crates/aspis-core/src/NDH_coretranscript.rs']=(E/'NDH_coretranscript.rs.txt').read_text()
 n='crates/aspis-r1-cost-probe/src/sampler.rs';b=base(n)
 b=b.replace('fn decode8(', '#[cfg_attr(kani,kani::requires(digits[0]<P&&digits[1]<P&&digits[2]<P&&digits[3]<P&&digits[4]<P&&digits[5]<P&&digits[6]<P&&digits[7]<P))]\n#[cfg_attr(kani,kani::ensures(|r| (r.to_limbs()==crate::NDH_reference::pack8_ref(digits)) != cfg!(NDH_invert_decode8)))]\nfn decode8(')
 b+='\n#[cfg(kani)]\n#[path="NDH_sampler.rs"]\nmod NDH_native;\n';out[n]=b
 out['crates/aspis-r1-cost-probe/src/NDH_sampler.rs']=(E/'NDH_sampler.rs.txt').read_text()
 inverted=os.environ.get('NDH_INVERT')
 if inverted:
  for n in out:out[n]=out[n].replace('cfg!(NDH_invert_'+inverted+')','true').replace('cfg!(NDH_bad_'+inverted+')','true')
 patch=[]
 for n,s in out.items():
  p=subprocess.run(['git','show',REV+':'+n],capture_output=True,text=True);b=p.stdout if p.returncode==0 else ''
  patch.append(''.join(difflib.unified_diff(b.splitlines(True),s.splitlines(True),fromfile='a/'+n if b else '/dev/null',tofile='b/'+n)))
 (E/'NDH_native.patch').write_text(''.join(patch));return out
if __name__=='__main__':files()
