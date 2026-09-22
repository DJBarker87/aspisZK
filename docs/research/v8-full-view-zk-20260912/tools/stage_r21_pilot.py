#!/usr/bin/env python3
"""Fresh source-only R21 pilot, pinned to the actual R20 clean-B source.

No production integration, keys, ELF copying, proof generation or deployment.
"""
import argparse,hashlib,json,re,shutil
from pathlib import Path
EX=Path('docs/research/v8-no-work-100-20260907/experiments')
ELF='fbaaab12e5f0e798dde28626abadb61cff69354cabb2dcf3f1125559efb2db8c'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def function(text,name):
    at=text.index('fn '+name+'(');start=text.index('{',at);depth=0
    for i in range(start,len(text)):
        if text[i]=='{':depth+=1
        elif text[i]=='}':
            depth-=1
            if depth==0:return text[at:i+1]
    raise ValueError(name)
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();src=a.stage.resolve();dst=a.output.resolve();here=Path(__file__).parent
    assert not dst.exists() and src not in dst.parents
    m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==173
    assert m['r20_execution']['instrumented'] is False
    for n,h in m['files'].items():
        path=(src/n).resolve();assert src in path.parents and sha(path)==h,n
    elf=src/'sbf-primary/aspis_v8_performance_sbf.so'
    if elf.exists():assert sha(elf)==ELF
    dst.mkdir()
    for n in ('crates','docs','programs','xtask'):
        shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('.git','target','*-keypair.json'))
    for n in ('Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',
              'audit/poseidon-pair-probe/program/Cargo.toml','audit/poseidon-pair-probe/program/src/lib.rs'):
        if (src/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
    for n,h in m['files'].items():
        if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
        assert sha(dst/n)==h,n
    changed=[]
    for n in ('r21_native.rs','r21_gkr.rs','r21_gkr_toy.rs','r21_trace_field.rs','r21_trace_main.rs'):
        shutil.copy2(here/n,dst/EX/n);changed.append(dst/EX/n)
    path=dst/EX/'performance-host/Cargo.toml'
    path.write_text(path.read_text()+'\n[[bin]]\nname="r21-trace"\npath="../r21_trace_main.rs"\n\n[[bin]]\nname="r21-gkr-toy"\npath="../r21_gkr_toy.rs"\n');changed.append(path)
    path=dst/EX/'r17_host_relation.rs';text=path.read_text()
    anchor='        let ordinary=crate::r19_channel_ordinary::terminal_shared(&public_audit,p.abc,alphas,beta,&mut workspace,&kernel);'
    assert text.count(anchor)==1
    text=text.replace(anchor,anchor+'''
        #[cfg(not(target_os="solana"))]
        if std::env::var_os("ASPIS_R21_CAPTURE_PUBLIC").is_some() {
            let mut inputs=public_audit.to_vec(); inputs.extend(p.abc); inputs.extend(alphas);
            inputs.push(beta); inputs.extend_from_slice(&finals[..4]); inputs.push(p.tau);
            assert_eq!(inputs.len(),24);
            eprintln!("R21_PUBLIC_INPUTS {{\\"fields\\":{:?}}}",bytes(&inputs));
        }
''')
    path.write_text(text);changed.append(path)
    provenance={'base_git_commit':'6f00e7f6c893c3a81bc37526e32d563434d303c8',
        'source_manifest_sha256':sha(src/'r18-stage.json'),'r20_source_pins_checked':173,
        'control_elf_sha256':ELF,'control_elf_present_and_checked':elf.exists(),
        'scope':'public ordinary+image pilot only; no original acceptance replacement',
        'source_changes':{str(f.relative_to(dst)):{'before':m['files'].get(str(f.relative_to(dst))),'after':sha(f)}for f in changed},
        'source_function_sha256':{name:hashlib.sha256(function((src/path).read_text(),name).encode()).hexdigest() for name,path in [
            ('image_terminal',EX/'relation_callback.rs'),('v6_statement_points',Path('crates/aspis-core/src/v6_transcript.rs'))]}}
    for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
    m['r21_pilot']=provenance
    (dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
    (dst/'r21-stage.json').write_text(json.dumps(provenance,indent=2)+'\n')
    print(json.dumps({'stage':str(dst),'pins':len(m['files']),'built':False}))
if __name__=='__main__':main()
