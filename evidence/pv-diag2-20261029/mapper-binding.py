from pathlib import Path
import json,hashlib,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');old=json.loads((D/'native-binding.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[old['source_rows'][1],old['source_rows'][2]]
for r in rows:assert sha(Path(r['path']))==r['sha256'] and r['body'] in Path(r['path']).read_text()
wire=D.parent/'codex-pv-fscan-20261028/src/crates/aspis-r1-cost-probe/src/r1_wire.rs';mask=D.parent/'codex-pv-fscan-20261028/src/crates/aspis-prover/src/state_only_hiding.rs'
for p,needle in [(wire,'pub enum Error'),(mask,'pub enum StateOnlyMaskBuildError')]:
 text=p.read_text();i=text.index(needle);assert '#[derive(Clone, Copy, Debug, PartialEq, Eq)]' in text[max(0,i-65):i]
src=D/'PV_DIAG2_MapperControl.rs';src.write_text('''use aspis_r1_cost_probe::{verifier::Error,r1_wire::Error as SError};
use aspis_prover::state_only_hiding::StateOnlyMaskBuildError;
'''+ '\n'.join(r['body'] for r in rows)+'''
fn main(){
 let mut n=0;
 let values=[SError::Allocation,SError::RowOrder{expected:0,actual:255},SError::InvalidRow,SError::Tag{row:255},SError::Length{row:0},SError::NonCanonical{row:255,value:usize::MAX},SError::Boundary{round:usize::MAX},SError::Terminal,SError::EqualCirclePoints,SError::TrailingBytes,SError::Public,SError::ActivePole];
 for e in values { assert_eq!(semantic_error(e),if matches!(e,SError::ActivePole){Error::Rejected}else{Error::Semantic});n+=1; }
 for e in [StateOnlyMaskBuildError::ZeroPrivateEntropy,StateOnlyMaskBuildError::ReusedMaskNonce,StateOnlyMaskBuildError::MaskSampleExhausted,StateOnlyMaskBuildError::TraceShape,StateOnlyMaskBuildError::Layout]{assert_eq!(mask_error(e),if matches!(e,StateOnlyMaskBuildError::MaskSampleExhausted){Error::Rejected}else{Error::Semantic});n+=1;}
 println!("{{\\\"cases\\\":{n}}}");
}
''')
T=D.parent/'codex-pv-rdea-20261028/client-target/release/deps';libs=[next(T.glob('lib'+name+'-*.rlib')) for name in ['aspis_r1_cost_probe','aspis_prover']];rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc';exe=D/'mapper-control';cmd=[rustc,'--edition=2021','--cfg','feature="r1p-check"','--cfg','feature="ct-host-prover"','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','-L','dependency='+str(T)]
for name,p in zip(['aspis_r1_cost_probe','aspis_prover'],libs):cmd+=['--extern',name+'='+str(p)]
cmd += [str(src),'-o',str(exe)];print('Expected time: optimized mapper compilation and finite enum controls',flush=True);subprocess.run(cmd,check=True);r=subprocess.run([str(exe)],capture_output=True,text=True);assert r.returncode==0
result=dict(classification='structural (K-1 substitute) complete local mapper binding plus finite native validation; no production attempt-silence claim',source_rows=rows,additional_sources={str(p):sha(p) for p in [wire,mask]},command=cmd,toolchain=subprocess.check_output([rustc,'-vV'],text=True),features='deployed r1p-check selected in helper and exact deployed dependency rlibs',profile='release opt3 debug/overflow assertions off panic unwind',rlibs={str(p):sha(p) for p in libs},generated_reference_sha256=sha(src),results=json.loads(r.stdout),binding=['copy enum argument has no drop glue','derived equality compares variants; comparing with unit ActivePole/MaskSampleExhausted reads no data payload fields','conditional selects unit Rejected or unit Semantic','let _=e has no owned destructor','no formatter, allocator, I/O, hook, log or capture call in this complete local primitive call closure','Lean complete-Result semantic_mapper_exact/mask_mapper_exact and local diagnostic silence semantic_mapper_silent/mask_mapper_silent; typed source primitives retain compiler boundary'],retained=['V370 / owner pending D381/D386 compiler-cohort boundary','error producer/caller effects and existing L1 V347-V351 joint event law','asynchronous runtime/foreign crash observations; timing/microarchitecture not classified by diagnostic-effect silence'])
(D/'semantic-mapper-binding.json').write_text(json.dumps(result,indent=2)+'\n');print(r.stdout)
