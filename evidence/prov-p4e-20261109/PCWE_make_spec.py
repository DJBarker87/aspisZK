#!/usr/bin/env python3
"""Build sources/<key>/ and PCWE_<run>_spec.json for the archive-linked cut modules of P4e.
Usage: PCWE_make_spec.py <key> <run>
All inputs are read from git objects of the worktree HEAD (never from the shared checkout, never from the host)."""
import sys,json,hashlib,subprocess,tarfile,io,gzip
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
WT=str(E.parent.parent)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(p):return subprocess.check_output(['git','-C',WT,'show','HEAD:'+p])
EV='docs/research/100bit-spend-path-20261013/evidence/'
XRA='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/'
CH=XRA+'charon'
CH_SHA='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
AE='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'
AE_SHA='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3'
AE_EXT=XRA+'aeneas-b59d5188-extended'
AE_EXT_SHA='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
def aeneas_cmd(aeneas,ns):
    return [aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest','{OUT}/raw','-subdir',ns,'-split-files','-emit-json','{OUT}/repro.llbc']
def env(tc,target,extra=None):
    e={'RUSTUP_TOOLCHAIN':tc,'CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':'{WS}/../PCWE_target_'+target,'CARGO_NET_OFFLINE':'true','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'}
    e.update(extra or {});return e

def arch_member(archive,prefix):
    blob=git(EV+archive);t=tarfile.open(fileobj=io.BytesIO(blob))
    out={}
    for ti in t:
        nm=ti.name[2:] if ti.name.startswith('./') else ti.name
        if ti.isfile() and nm.startswith(prefix):out[nm[len(prefix):]]=t.extractfile(ti).read()
    return sha(blob),out

def tarball(files,path):
    buf=io.BytesIO()
    with tarfile.open(fileobj=buf,mode='w') as t:
        for rel in sorted(files):
            ti=tarfile.TarInfo(rel);ti.size=len(files[rel]);ti.mtime=0;ti.uid=ti.gid=0;ti.uname=ti.gname='';ti.mode=0o644
            t.addfile(ti,io.BytesIO(files[rel]))
    raw=buf.getvalue()
    gz=io.BytesIO()
    with gzip.GzipFile(fileobj=gz,mode='wb',mtime=0,compresslevel=9) as g:g.write(raw)
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(gz.getvalue())
    return sha(gz.getvalue())

def build(key,run):
    d=E/'sources'/key
    if key=='prefix_e':
        R=EV+'r18-prefix-aggregate-extraction-20261016/extraction/prefix-e-exact/'
        names=['Cargo.toml','Cargo.lock','lib.rs','extract.py','source-pins.json']
        files={};
        for n in names:
            b=git(R+'source/'+n);(d/n).parent.mkdir(parents=True,exist_ok=True);(d/n).write_bytes(b)
            files[n]=dict(sha256=sha(b),local=f'sources/{key}/{n}',git='HEAD:'+R+'source/'+n)
        spec=dict(run=run,spec_id=key,frozen_workspace=False,crate_dir='crate',
          charon_command=[CH,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option','--include','core::result::Result','--start-from','crate::r1_wire','--dest-file','{OUT}/repro.llbc','--','--locked','--offline','--release','--lib','--no-default-features'],
          aeneas_command=aeneas_cmd(AE,'AspisR1PrefixAggregateParser'),
          env=env('nightly-2026-06-01','prefix_e',{'NO_DNA':'1'}),namespace='AspisR1PrefixAggregateParser',
          expected_tool_sha256={CH:CH_SHA,AE:AE_SHA},
          archive=dict(evidence=EV+'r18-prefix-aggregate-extraction-20261016/extraction/prefix-e-exact/',llbc='PrefixInto.llbc.gz',generated='generated/AspisR1PrefixAggregateParser/{Funs,Types}.lean'),
          recorded_original_tools=dict(charon='aspis-r1-r18-tools-20261016/charon-target/release/charon (tool-inventory.json); host now has XRa_bin/charon daad69be (equal to the sha recorded by other r18 receipts)',aeneas='aspis-r1-r18-tools-20261016/bin/aeneas; P4c rebuilt 959659a6 (matches the recorded sha)'),
          recorded_original_environment='archive environment.json: PATH with toolchain bin first, LD_LIBRARY_PATH toolchain lib, RUSTUP_TOOLCHAIN nightly-2026-06-01, CARGO_BUILD_JOBS 1, CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS true (ON), CARGO_NET_OFFLINE true, NO_DNA 1; cwd = source dir',
          files=files)
    elif key=='adapter':
        arch='adapter-reconstruct-432-20261016/source-extraction-proofs.tar.gz'
        ablob,fl=arch_member(arch,'input/')
        # manifest of the whole input tree
        tgz=tarball(fl,d/'adapter_input.tar.gz')
        files={rel:dict(sha256=sha(b)) for rel,b in fl.items()}
        spec=dict(run=run,spec_id=key,frozen_workspace=False,crate_dir='input',
          input_tar=dict(local=f'sources/{key}/adapter_input.tar.gz',sha256=tgz,source=EV+arch+' member prefix input/ (blob sha256 %s)'%ablob,deterministic='sorted names, mtime 0, uid/gid 0, mode 0644, gzip mtime 0 level 9'),
          charon_command=[CH,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','aspis_statement','--include','aspis_core::field','--include','solana_program_error','--include','core::option','--include','core::result::Result','--include','core::result::_::map_err','--start-from','crate::r1_pool_adapter::reconstruct_asq8_statement','--dest-file','{OUT}/repro.llbc','--','--locked','--offline','--release','-p','aspis-r1-adapter-reconstruct','--lib','--no-default-features','--features','pool-adapter,private-leaf-salts'],
          aeneas_command=aeneas_cmd(AE,'AspisR1AdapterReconstruct'),
          env=env('nightly-2026-06-01','adapter',{'CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL':'3'}),namespace='AspisR1AdapterReconstruct',
          expected_tool_sha256={CH:CH_SHA,AE:AE_SHA},
          archive=dict(archive=EV+arch,llbc='extraction-a/AdapterReconstruct.llbc',generated='extraction-a/generated/AspisR1AdapterReconstruct/{Funs,Types,FunsExternal_Template}.lean',receipts='runs/charon-a, runs/aeneas-a'),
          recorded_original_tools=dict(charon='aspis-r1-r18-tools-20261016/charon-target/release/charon',aeneas='aspis-r1-r18-tools-20261016/bin/aeneas (959659a6 rebuilt by P4c)'),
          recorded_original_environment='runs/charon-a/environment.json: RUSTUP_TOOLCHAIN nightly-2026-06-01, CARGO_BUILD_JOBS 1, CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS true (ON), CARGO_TARGET_DIR native-target, CHARON_TOOLCHAIN_IS_IN_PATH unset by env -u, CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3 set on the charon command line; cwd = input workspace root',
          files=files)
    else:
        raise SystemExit('unknown key '+key)
    (E/(run+'_spec.json')).write_text(json.dumps(spec,indent=1)+'\n')
    print(run,key,len(spec['files']),'files')

if __name__=='__main__':build(sys.argv[1],sys.argv[2])
