#!/usr/bin/env python3
"""Diagnostic markers only; never use this ELF for a clean budget claim."""
import argparse,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert 'r24_compose' in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
path=ex/'relation_callback.rs';path.write_text(path.read_text()+'''
#[inline(always)] fn r24_tick(s:&'static str) {
    #[cfg(target_os="solana")] {solana_program::log::sol_log(s);solana_program::log::sol_log_compute_units();}
    #[cfg(not(target_os="solana"))] let _=s;
}
''');changed.append(path)
path=ex/'performance_verifier.rs';text=path.read_text()
for old,new in [('let mut semantic_basis=vec![K::ZERO;271];','crate::r24_tick("R24:start");\n    let mut semantic_basis=vec![K::ZERO;271];'),('let prepared=crate::r17_relation::prepare_compact(s,w).map_err(|_|5u32)?;','crate::r24_tick("R24:semantic");\n    let prepared=crate::r17_relation::prepare_compact(s,w).map_err(|_|5u32)?;\n    crate::r24_tick("R24:prepare");'),('let result=crate::r17_relation::verify_cached(w,prepared,false,Some(&semantic_basis));','let result=crate::r17_relation::verify_cached(w,prepared,false,Some(&semantic_basis));\n    crate::r24_tick("R24:complete");')]:
    assert text.count(old)==1;text=text.replace(old,new)
for label in ['semantic-rounds','semantic-terminal']:
    old=f'checkpoint("v8:{label}");';assert text.count(old)==1;text=text.replace(old,f'crate::r24_tick("R24:{label}");')
path.write_text(text);changed.append(path)
path=ex/'r17_host_relation.rs';text=path.read_text();start=text.index('pub(super) fn opened_channel(');end=text.index('\npub(super) fn ',start+1)
part=text[start:end];pattern=r'#\[cfg\(target_os="solana"\)\]\s*\{\s*\(\);\s*\(\);\s*\}'
labels=iter(['R24:opening-points','R24:opening-records','R24:merkle']);assert len(re.findall(pattern,part))==3
part=re.sub(pattern,lambda _:f'crate::r24_tick("{next(labels)}");',part);text=text[:start]+part+text[end:]
start=text.index('pub(super) fn verify_cached(');part=text[start:];labels=iter(['R24:before-openings','R24:after-openings','R24:query-tail','R24:ordinary','R24:terminal'])
assert len(re.findall(pattern,part))==5
part=re.sub(pattern,lambda _:f'crate::r24_tick("{next(labels)}");',part);path.write_text(text[:start]+part);changed.append(path)
for path in changed:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_profile']={'control_manifest_sha256':sha(src/'r18-stage.json'),'instrumented':True,'budget_claim_allowed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
