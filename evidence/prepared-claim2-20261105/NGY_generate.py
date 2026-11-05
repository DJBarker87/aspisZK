from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent; rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files=['verifier.rs','fast_pairing.rs','r1_wire.rs','lib.rs']
frozen={n:subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/'+n],text=True) for n in files}
# The ONLY substitution inside the native cut is the ruled-(y) oracle call.
s=frozen['verifier.rs'];lines=s.splitlines();cut='\n'.join(lines[58:60]);assert 'let scalar=match point' in cut and 'dot.push' in cut
native=cut.replace('dot.push(g[l],scalar)','oracle(&mut dot,g[l],scalar,post,reply,&mut log)')
rs=(E/'NGY_native.rs.txt').read_text().replace('// NGY_FROZEN_CUT',native)
payload={'crates/aspis-r1-cost-probe/src/verifier.rs':s+'\n#[cfg(kani)]\n#[path="NGY_stages.rs"]\nmod NGY_stages;\n','crates/aspis-r1-cost-probe/src/NGY_stages.rs':rs}
f=frozen['fast_pairing.rs'];f=f.replace('    pub struct Dot { sums:[u64;4] }','''    pub struct Dot { sums:[u64;4] }
    #[cfg(kani)] impl Dot {
      pub(super) fn NGY_from(sums:[u64;4])->Self{Self{sums}}
      pub(super) fn NGY_sums(&self)->[u64;4]{self.sums}
    }''')
f+='''
#[cfg(kani)] pub mod NGY_carrier {
 use super::*;
 pub fn from(s:[u64;8],count:usize)->EbyKDot{EbyKDot{c0:canonical::Dot::NGY_from([s[0],s[1],s[2],s[3]]),c1:canonical::Dot::NGY_from([s[4],s[5],s[6],s[7]]),count}}
 pub fn get(d:&EbyKDot)->([u64;8],usize){let a=d.c0.NGY_sums();let b=d.c1.NGY_sums();([a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]],d.count)}
}
''';payload['crates/aspis-r1-cost-probe/src/fast_pairing.rs']=f
w=frozen['r1_wire.rs']+'''
#[cfg(kani)] pub mod NGY_carrier {
 use super::*;
 pub fn from<H:Digest32>(state:[u8;32],hash:H,next_row:u8)->SemanticTranscript<H>{SemanticTranscript{state,hash,next_row}}
}
''';payload['crates/aspis-r1-cost-probe/src/r1_wire.rs']=w
payload['crates/aspis-r1-cost-probe/src/lib.rs']='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen['lib.rs']
(E/'NGY_PAYLOAD.json').write_text(json.dumps(payload))
patch=''
for n,t in payload.items():
 old=frozen.get(Path(n).name,'');patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NGY_HARNESS.patch').write_text(patch)
pins=json.loads((E.parent/'prepared-claim-20261105/NGU_SOURCE_PINS.json').read_text())
pins.pop('crates/aspis-r1-cost-probe/src/NGU_stages.rs',None)
pins['crates/aspis-r1-cost-probe/src/lib.rs']=hashlib.sha256(subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/lib.rs'])).hexdigest()
for n in list(pins):
 if n in payload:pins[n]=hashlib.sha256(payload[n].encode()).hexdigest()
(E/'NGY_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NGY_CUT.json').write_text(json.dumps(dict(revision=rev,lines=[59,60],frozen_cut=cut,oracle_cut=native,frozen_verifier_sha256=hashlib.sha256(s.encode()).hexdigest(),patch_sha256=hashlib.sha256(patch.encode()).hexdigest()),indent=1)+'\n')
