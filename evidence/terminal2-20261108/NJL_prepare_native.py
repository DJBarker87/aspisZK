from pathlib import Path
import subprocess,json,hashlib,lzma,difflib,base64
E=Path(__file__).resolve().parent;P=E.parent/'terminal-20261107';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
manifest=json.loads((P/'NJB_STAGING_MANIFEST.json').read_text());files={}
for n,r in manifest['files'].items():
 raw=subprocess.check_output(['git','show',rev+':'+n]);assert hashlib.sha256(raw).hexdigest()==r['sha256'];files[n]=base64.b64encode(raw).decode()
raw=json.dumps(files).encode();(E/'NJL_FROZEN_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'NJL_FROZEN_INPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NJL_STAGING_MANIFEST.json').write_text(json.dumps(manifest))
(E/'NJL_KMX.patch').write_bytes((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
source=base64.b64decode(files['crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs']).decode();start=source.index('fn active_mask_basis(');stop=source.index('\n    #[inline(always)]',start);body=source[start:stop]
# Control decomposition: only arithmetic/read-write windows replaced. Retain loop guards/increments verbatim.
ha=body.index('        while block <');hb=body.index('        let mut sum',ha);la=body.index('        while coordinate <',hb);lb=body.rindex('        sum')
high=body[ha:hb];low=body[la:lb]
hc=high[:high.index('\n')+1]+'''            log.enter(block);
            block += 1;
        }
'''
lc=low[:low.index('\n')+1]+'''            log.enter(64+coordinate);
            coordinate += 1;
        }
'''
header='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct NJL_Control { seek:usize, seen:usize, calls:usize }
impl NJL_Control { fn enter(&mut self,position:usize) { if self.calls==self.seek {self.seen=position;} self.calls+=1; } }
fn NJL_active_control(log:&mut NJL_Control)->([QM31;7],QM31,usize,usize){
 const MASKS:[u16;7]=[6144,6145,4097,2048,2049,26214,1749];
 let high_sums=[QM31::ZERO;MASKS.len()];
 let mut block=0usize;
'''
code=header+hc+' let sum=QM31::ZERO;\n let mut coordinate=0usize;\n'+lc+' (high_sums,sum,block,coordinate)\n}\n'+'''
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_active_control_cut(){
 let seek:usize=kani::any();kani::assume(seek<71);
 let mut log=NJL_Control{seek,seen:999,calls:0};
 let (high,sum,block,coordinate)=NJL_active_control(&mut log);
 assert_eq!(log.calls,71);assert_eq!(block,64);assert_eq!(coordinate,7);
 assert_eq!(log.seen,seek ^ if cfg!(NJL_invert){1}else{0});
 let cell:usize=kani::any();kani::assume(cell<7);
 assert_eq!(high[cell],QM31::ZERO);assert_eq!(sum,QM31::ZERO);
}
'''
(E/'NJL_control.rs.txt').write_text(code)
(E/'NJL_CONTROL_ERASURE.json').write_text(json.dumps(dict(source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs',revision=rev,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),original_high_loop=high,original_low_loop=low,control_high_loop=hc,control_low_loop=lc,removed_windows='high read/match/add/store and low match/mul/add only; guards and increments verbatim',observed='all71 source positions via arbitrary seek; zero initializers, exit counters'),indent=2))
n='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';append='\n#[cfg(kani)]\n#[path="NJL_control.rs"]\nmod NJL_native;\n';original=base64.b64decode(files[n]).decode();new=original+append
patch=''.join(difflib.unified_diff(original.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n));patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NJL_control.rs'));(E/'NJL_native.patch').write_text(patch)
(E/'NJL_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(new.encode()).hexdigest(),'crates/aspis-statement/src/pool_v1/NJL_control.rs':hashlib.sha256(code.encode()).hexdigest()}))
(E/'NJL_FROZEN_FILE_PINS.json').write_text(json.dumps({n:r['sha256']for n,r in manifest['files'].items()}))
(E/'NJL_stage_native.py').write_text('''from pathlib import Path
import json,lzma,hashlib,subprocess,base64
b=Path(__file__).resolve().parent;s=b/'NJL_src';s.mkdir(exist_ok=True)
raw=lzma.decompress((b/'NJL_FROZEN_INPUTS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(b/'NJL_FROZEN_INPUTS.json.sha256').read_text().strip()
for n,text in json.loads(raw).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),str(p);p.write_bytes(base64.b64decode(text))
for patch in ['NJL_KMX.patch','NJL_native.patch']:
 subprocess.run(['git','apply','--check',str(b/patch)],cwd=s,check=True)
 subprocess.run(['git','apply',str(b/patch)],cwd=s,check=True)
print('Frozen scratch staged; exact KMX and cfg-only control module applied')
''')
# Preserve the predecessor strict graph/source/lock validator; rename only own paths.
gate=(P/'NJB_gate.py').read_text().replace('NJB_','NJL_');(E/'NJL_gate.py').write_text(gate)
base=json.loads((E/'NJL_L005.json').read_text());B='/home/dombarker/project-offloads/codex-cx-terminal2-20261108';base.update(attempt='NJL_L006',kind='setup',module='NJL_stage_native',sources=['NJL_stage_native.py','NJL_FROZEN_INPUTS.json.xz','NJL_FROZEN_INPUTS.json.sha256','NJL_STAGING_MANIFEST.json','NJL_KMX.patch','NJL_native.patch','NJL_SOURCE_PINS.json','NJL_FROZEN_FILE_PINS.json','NJL_CONTROL_ERASURE.json','NJL_control.rs.txt'],command=['python3','NJL_stage_native.py'],collect=[],deps_fingerprint={},expected_time='Small frozen scratch staging, no prover/extraction; reused predecessor emission only');(E/'NJL_L006.json').write_text(json.dumps(base))
for k in [1,2]:
 x=json.loads((P/'NJB_K020.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_active_control_cut',sources=['NJL_gate.py','NJL_SOURCE_PINS.json','NJL_FROZEN_FILE_PINS.json','NJL_control.rs.txt','NJL_CONTROL_ERASURE.json','NJL_native.patch','NJL_KMX.patch'],command=['python3','NJL_gate.py',a+'.json'],deps_fingerprint={},expected_time='Optimized frozen active loop CONTROL only; arithmetic windows already certified by NJB. Compilation then one named control-sequence elimination')
 x['native_command']=[v.replace('codex-cx-terminal-20261107','codex-cx-terminal2-20261108').replace('NJB_src','NJL_src').replace('NJB_target','NJL_target').replace('pool_v1::pair_forest_copy_terminal::NJB_active_native::NJB_active_low','pool_v1::pair_forest_copy_terminal::NJL_native::NJL_active_control_cut') for v in x['native_command']]
 x['env']['TMPDIR']=B+'/NJL_tmp';x['env']['CARGO_TARGET_DIR']=B+'/NJL_target';x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJL_invert'if k==2 else '')
 x['collect']=[v.replace('NJB_K020',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
print('Frozen payload compressed, control and erasure inputs retained')
