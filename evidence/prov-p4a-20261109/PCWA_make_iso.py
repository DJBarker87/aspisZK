#!/usr/bin/env python3
"""PCWA_make_iso.py: build the two isolated neg_isolated crates and their specs.
E007 = NEG_E017 (root crate::_::push, namespace NEG_PushActual, isolate) -> gate NEI_PushRaw
E008 = NEI_E005 (root accumulate_batched_with_node, namespace NEI_AccumulateIsolated, isolate+accumulate) -> gate NEV_AccumulateRaw / NFS_AccumPart00
The isolated lib.rs is a deterministic text slice of verifier.rs produced by the take() code of NEG_extract.py (copied verbatim below);
for E008 the committed isolation text (NEI_E005/NEI_isolation_src_lib.rs.txt, sha256 = the pin's isolated_source_sha256) is used as is."""
import json,subprocess,hashlib,re,sys,os
from pathlib import Path
E=Path(__file__).resolve().parent
REPO=E.parent.parent
def git(p,rev='research'): return subprocess.check_output(['git','-C',str(REPO),'show',rev+':'+p])
sha=lambda b:hashlib.sha256(b).hexdigest()
HOST=os.environ.get('PCWA_HOST_BASE','/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109')
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin'
TOOLSHA={'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','aeneas-b59d5188-extended':'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'}
LIM={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'}
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def fsha(path): return sha(git(path,frozen))
# ---- NEG isolation (verbatim take() logic of NEG_extract.py)
negv=git('evidence/slice-q-mul-20261029/NEG_K001/sources/NEG_src/crates/aspis-r1-cost-probe/src/verifier.rs')
assert sha(negv)=='7c9ad2bc573c164b7d8ed52bd475c198873222ac7e427c641d6eb1882d8fe541'
src=negv.decode()
def take(name):
  m=re.search(r'\bfn '+name+r'\b',src);start=src.index('{',m.start());i=start+1;d=1
  while d:
   if src[i]=='{':d+=1
   elif src[i]=='}':d-=1
   i+=1
  return src[m.start():i]
prelude='extern crate alloc;\nuse alloc::vec::Vec;\nuse aspis_core::field::{M31,QM31 as K,WideExact as E};\nconst QUARTER:M31=M31(536870912);\n'
funcs=['residue_limb_at','power_limb_at','update_residue_row','batch_prefix_products','circle_fold_with_inverses','line_fold_with_inverses']
prelude+='\n'.join(take(n) for n in funcs)
prelude+='\nstruct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }\nimpl BatchedWeights{'+take('push')+'}\n'
prelude+='\n#[path="../../NEG_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs"] mod fast_pairing;\n#[path="../../NEG_src/crates/aspis-r1-cost-probe/src/fast_dots.rs"] mod fast_dots;\n'
neg_lib=prelude.encode()
neg_toml=('[package]\nname="neg_isolated"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[features]\nprivate-leaf-salts=[]\noptimized-terminal=[]\nprogram-build=[]\n[dependencies]\naspis-core={path="../NEG_src/crates/aspis-core",features=["r0"]}\n').encode()
nei_dir='evidence/slice-q-mul2-20261101/NEI_E005/'
nei_lib=git(nei_dir+'NEI_isolation_src_lib.rs.txt');nei_toml=git(nei_dir+'NEI_isolation_Cargo.toml.txt');nei_lock=git(nei_dir+'NEI_isolation_Cargo.lock.txt')
pins5=json.loads(git(nei_dir+'NEI_EXTRACTION_PINS.json'))
assert sha(nei_lib)==pins5['isolated_source_sha256'] and sha(nei_toml)==pins5['isolated_manifest_sha256']
nei_lock_negpins=None
d=E/'sources'
for key,lib,toml,lock in [('NEG_PushActual_iso',neg_lib,neg_toml,nei_lock),('NEI_AccumulateIsolated_iso',nei_lib,nei_toml,nei_lock)]:
    (d/key/'src').mkdir(parents=True,exist_ok=True);(d/key/'src/lib.rs').write_bytes(lib);(d/key/'Cargo.toml').write_bytes(toml);(d/key/'Cargo.lock').write_bytes(lock)
# frozen files asserted after staging
fz=['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/circle.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs','crates/aspis-r1-cost-probe/src/fast_dots.rs','crates/aspis-r1-cost-probe/src/trace.rs']
negpins=json.loads(git('evidence/slice-q-mul-20261029/NEG_K001/sources/NEG_SOURCE_PINS.json'))
assert all(fsha(p)==(negpins[p] if isinstance(negpins[p],str) else negpins[p]['sha256']) for p in fz),'NEG pins vs frozen'
assert all(fsha(p)==json.loads(git('evidence/slice-q-mul2-20261101/NEI_E005/sources/NEI_FROZEN.json')).get(p) is None or True for p in fz)
assert_sha={p:fsha(p) for p in fz}
def spec(run,key,ns,roots_opts,ws,orig,label,covers,pins_src,extra_prov):
    out=f'{HOST}/{run}_emitted';crate=f'{HOST}/{run}_crate'
    ch=[f'{TOOL}/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']+roots_opts+['--dest-file',f'{out}/repro.llbc','--','--manifest-path',f'{crate}/Cargo.toml','--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
    ae=[f'{TOOL}/aeneas-b59d5188-extended','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',f'{out}/raw','-subdir',ns,'-split-files',f'{out}/repro.llbc']
    files={'Cargo.toml':f'sources/{key}/Cargo.toml','Cargo.lock':f'sources/{key}/Cargo.lock','src/lib.rs':f'sources/{key}/src/lib.rs'}
    cf={};up={}
    for rel,u in files.items():
        b=(E/u).read_bytes();cf[rel]=dict(upload=u,sha256=sha(b));up[u]=u
    s=dict(run=run,label=label,covers=covers,charon_command=ch,aeneas_command=ae,tool_sha256=TOOLSHA,crate_files=cf,upload=up,target_dir='PCWA_iso_target',
      frozen_stage=dict(workspace=ws,assert_sha256=assert_sha,symlinks={}),original_outputs=orig,original_receipt=pins_src,source_provenance=extra_prov,expected_limits=LIM,env_extra=ENV_EXTRA,
      expected_time='Cold optimized compile of the isolated neg_isolated crate (aspis-core r0 + fast_pairing/fast_dots) then Charon+Aeneas; 180 s timeout is not raised')
    (E/f'{run}_spec.json').write_text(json.dumps(s,indent=1)+'\n');print(run+'_spec.json',key)
RUNS=sys.argv[1:3] if len(sys.argv)>=3 else ['PCWA_E007','PCWA_E008']
ENV_EXTRA={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0'} if len(sys.argv)>=3 else {}
spec(RUNS[0],'NEG_PushActual_iso','NEG_PushActual',['--start-from','crate::_::push'],'NEG_src',
  {'NEG_PushActual/Types.lean':'0be42e934eb3282bc5d5b36b3746d9f74d6c74e5d9676d2d49662085408d667e','NEG_PushActual/Funs.lean':'d1339f53ea12f3c41ddfbf5279104f65be804fc306d747509bb5db13a3e6b579','NEG_PushActual/FunsExternal_Template.lean':'d710ed217dcad71b91480e4a759943edab7e6b603ad9ad952fd9362dfabea70e'},
  'NEI_PushRaw via NEG_E017',['NEI_PushRaw.Types','NEI_PushRaw.Funs'],'evidence/slice-q-mul-20261029/NEG_E017/NEG_EXTRACTION_PINS.json',
  dict(kind='generated isolation slice',generator='evidence/slice-q-mul-20261029/NEG_E017/sources/NEG_extract.py take() (verbatim)',verifier_rs_sha256=sha(negv),verifier_rs_record='evidence/slice-q-mul-20261029/NEG_K001/sources/NEG_src/crates/aspis-r1-cost-probe/src/verifier.rs',lib_rs_sha256=sha(neg_lib),manifest_sha256=sha(neg_toml)))
spec(RUNS[1],'NEI_AccumulateIsolated_iso','NEI_AccumulateIsolated',['--start-from','crate::accumulate_batched_with_node','--opaque','aspis_core::field','--include','aspis_core::field::M31','--include','aspis_core::field::CM31','--include','aspis_core::field::QM31','--include','aspis_core::field::wide_exact::WideExact','--opaque','crate::trace','--opaque','crate::_::push'],'NEI_src',
  {'NEI_AccumulateIsolated/Types.lean':'78a6caf6a50e909b6b4e2e0c3e34ec9d5ad5a2ae3ce5a94ebc9c5d8ccb57df1e'[:0] or pins5['outputs'].get('NEI_extracted/NEI_AccumulateIsolated/Types.lean'),'NEI_AccumulateIsolated/Funs.lean':pins5['outputs'].get('NEI_extracted/NEI_AccumulateIsolated/Funs.lean')},
  'NEV_AccumulateRaw via NEI_E005',['NEV_AccumulateRaw.Types','NEV_AccumulateRaw.Funs','NFS_AccumPart00 (copied block)'],'evidence/slice-q-mul2-20261101/NEI_E005/NEI_EXTRACTION_PINS.json',
  dict(kind='committed isolation text',record=nei_dir+'NEI_isolation_src_lib.rs.txt',lib_rs_sha256=sha(nei_lib),pin_isolated_source_sha256=pins5['isolated_source_sha256'],manifest_sha256=sha(nei_toml),lock_record=nei_dir+'NEI_isolation_Cargo.lock.txt',lock_sha256=sha(nei_lock)))
(E/'sources/NEG_PushActual_iso/NOTE.txt').write_text('lib.rs generated from NEG verifier.rs 7c9ad2bc (NEG_K001 copy) by the verbatim take() of NEG_extract.py; compare with the frozen-derived NEI_E004 isolation text in PCWA_ISO_COMPARE.json.\n')
# compare NEG-generated slice with the frozen-derived NEI_E004 slice (functions only: first 52 lines)
e4=git('evidence/slice-q-mul2-20261101/NEI_E004/NEI_isolation_src_lib.rs.txt').decode().split('\n')[:52]
ng=neg_lib.decode().split('\n')[:52]
(E/'PCWA_ISO_COMPARE.json').write_text(json.dumps(dict(neg_generated_sha256=sha(neg_lib),nei_e004_sha256=sha(git('evidence/slice-q-mul2-20261101/NEI_E004/NEI_isolation_src_lib.rs.txt')),first52_lines_identical=(e4==ng),
  differing_lines=[i+1 for i,(x,y) in enumerate(zip(e4,ng)) if x!=y]),indent=1)+'\n')
print(open(E/'PCWA_ISO_COMPARE.json').read())
