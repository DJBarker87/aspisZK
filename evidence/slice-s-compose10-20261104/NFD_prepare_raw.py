"""Unrestricted raw carrier for actual frozen WideExact getters, scratch only."""
from NFD_native_patch import E,frozen,program
import subprocess,sys,json,difflib
shape,mode=sys.argv[1:];assert shape in ['limbs','bytes','tag'] and mode in ['positive','value','frame']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFD_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFD_KMX::KMX_copy_from_slice)]
'''
if shape=='tag':
 code='use aspis_r1_cost_probe::transport::Variant;let selector:u8=kani::any();kani::assume(selector<3);let v=match selector{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};assert!(v.tag()==(selector+1)'+('^1' if mode=='value' else '')+');'
 body=attrs+'fn raw(){'+code+'}\n';program(body,'NFD_raw');original=frozen('crates/aspis-r1-cost-probe/src/transport.rs')
else:
 if shape=='limbs':
  code='let words:[u32;8]=kani::any();let x=aspis_core::field::NFD_access::make(words);let i:usize=kani::any();kani::assume(i<8);assert!(x.to_limbs()[i]==words[i]'+('^1' if mode=='value' else '')+');'
 else:
  code='let mut bytes:[u8;32]=kani::any();let words:[u32;8]=kani::any();let x=aspis_core::field::NFD_access::make(words);let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<8&&j<32);let old=bytes[j];let value=words[k].to_le_bytes();{let mut iter=bytes.chunks_exact_mut(4).zip(x.to_limbs());let (chunk,limb)=iter.nth(k).unwrap();assert!(limb==words[k]&&chunk.len()==4);chunk.copy_from_slice(&limb.to_le_bytes());}let expected=if 4*k<=j&&j<4*k+4{value[j-4*k]}else{old};assert!(bytes[j]==expected'+('^1' if mode=='value' else '')+');'
  if mode=='value':code=code.replace('let old=bytes[j];','kani::assume(4*k<=j&&j<4*k+4);let old=bytes[j];')
  if mode=='frame':code=code.replace('let old=bytes[j];','kani::assume(j==(4*k+4)%32);let old=bytes[j];').replace('let expected=','bytes[(4*k+4)%32]^=1;let expected=')

 body=attrs+'fn raw(){'+code+'}\n';program(body,'NFD_raw')
 p='crates/aspis-core/src/field/wide_exact.rs';original=frozen(p)
 raw='''\n#[cfg(kani)]
pub mod NFD_raw {
use super::*;
pub fn make(w:[u32;8])->WideExact { WideExact{c0:QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}},c1:QM31{c0:CM31{a:M31(w[4]),b:M31(w[5])},c1:CM31{a:M31(w[6]),b:M31(w[7])}}} }
}
'''
 patch=''.join(difflib.unified_diff(original.splitlines(True),(original+raw).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
 p='crates/aspis-core/src/field.rs';f=frozen(p);added='\n#[cfg(kani)]\npub mod NFD_access { pub use super::wide_exact::NFD_raw::make; }\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),(f+added).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
 q=E/'NFD_native_contracts.patch';q.write_text(q.read_text()+patch)
(E/'NFD_RAW_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,source=body,domain='all eight raw u32 words, no canonicality restriction' if shape=='limbs' else 'every variant' if shape=='tag' else 'one arbitrary32-byte prestate and raw limb; one native iterator/copy body at k<8 with observed j<32',classification='raw carrier native getter/one serialization iteration; physical carrier/model certificate required separately'),indent=1)+'\n')
