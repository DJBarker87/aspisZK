"""One actual zip/chunks/copy iteration plus existing symbolic stride-four induction."""
import subprocess
import NFD_validate as v
from NFD_bridge_checks import REV
from NFD_composition_support import source,structural
from NFD_native_checks import native
E=v.E
F='crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes'
M31='crates/aspis-core/src/field.rs::M31::to_le_bytes'
RESOLVED={M31:'limb is u32 from to_limbs()->[u32;8]; native primitive u32::to_le_bytes, no M31 call',F:'limb is u32 from to_limbs()->[u32;8]; no recursive WideExact::to_le_bytes call'}
THMS=['NFD_WideSerialization.carrier_roundtrip','NFD_WideSerialization.result_state_effects']
ATTEMPTS=['NFD_K131','NFD_K132','NFD_K133']
EXTRAS=['NFD_RAW_SOURCE_DIGESTS.json']
CLASS='actual raw eight-word getter and one arbitrary-prestate native zip/chunks/copy iteration; disjoint stride-four frame and existing P6 induction; conservative M31/self alternatives resolved to primitive u32'
DOMAIN='all raw eight-u32 WideExact carriers; arbitrary32-byte prestate and observed j<32 at iteration k<8; no canonicality restriction'
DIGESTS={'NFD_K131': 'c3a7d870b735ed71fea2e83533d41034d8122690639430de77501fc2f3aff2a3', 'NFD_K132': '9fe5c8506a4cc287e789741d3c3bca359c188d94adbdb89294656b08351e1f07', 'NFD_K133': '02b465aa6520a0646d6d2ad964574ec5e3a5c8dd5bba6491a7bf1df79a09eb89'}
def check(c,base):
 assert c['subject']==F and c['resolved_non_calls']==RESOLVED
 assert c['native_certificate']==dict(function=F,complete=True,domain=DOMAIN,step=['NFD_K131','NFD_K132','NFD_K133'],callee='crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs')
 f=subprocess.check_output(['git','show',REV+':crates/aspis-core/src/field/wide_exact.rs'],text=True)
 assert 'pub const fn to_limbs(self) -> [u32; Self::LIMB_COUNT]' in f and 'pub const LIMB_COUNT: usize = 8;' in f
 a=f.index('    pub fn to_le_bytes(self)');body=f[a:f.index('\n    }',a)+6]
 assert body=='    pub fn to_le_bytes(self) -> [u8; Self::BYTE_LEN] {\n        let mut bytes = [0; Self::BYTE_LEN];\n        for (chunk, limb) in bytes.chunks_exact_mut(4).zip(self.to_limbs()) {\n            chunk.copy_from_slice(&limb.to_le_bytes());\n        }\n        bytes\n    }'
 for a,mode in zip(ATTEMPTS,['positive','value','frame']):
  snap=native(a,mode=='positive');m=v.read(E/(a+'-shape.json'));s=source(snap['NFD_native_contracts.patch'],'NFD_raw')
  assert m['shape']=='bytes' and m['mode']==mode and s==m['source'] and v.sha(s.encode())==DIGESTS[a]
  assert '.chunks_exact_mut(4).zip(x.to_limbs())' in s and 'iter.nth(k).unwrap()' in s
  assert 'chunk.copy_from_slice(&limb.to_le_bytes())' in s and 'limb==words[k]&&chunk.len()==4' in s
 return structural(c,F,THMS,base,ATTEMPTS,EXTRAS,CLASS)
