#!/usr/bin/env python3
"""Private canonical norm path with an independently retained inverse."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='1455a58e904b3b803c46de43686c73733b5c58a69f1bf391cc5d5190fbb1a296'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def save(n,s):
    f=ex/n;f.write_text(s);changed.append(f)
save('r110_norm.rs',(here/'r110_norm.rs').read_text())
f=ex/'line_norm.rs';s=f.read_text();old='fn norm_inverse(selected:';assert s.count(old)==1
s=s.replace(old,'fn r110_retained_norm(selected:')
s+='''
#[path="r110_norm.rs"]mod r110_norm;
fn norm_inverse(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31])->Result<(Vec<CM31>,Vec<M31>),Error>{
    if let Some(out)=r110_norm::try_norm(selected,values,abc,base,lines){
        #[cfg(not(target_os="solana"))] assert_eq!(out,r110_retained_norm(selected,values,abc,base,lines));
        return out;
    }
    r110_retained_norm(selected,values,abc,base,lines)
}
#[cfg(not(target_os="solana"))]pub(super)fn r110_controls(){r110_norm::controls();}
''';save(f.name,s)
for name,nextmod in [('joined_inverse.rs','line_norm'),('circle_norm.rs','joined_inverse')]:
    f=ex/name;save(name,f.read_text()+f'\n#[cfg(not(target_os="solana"))]pub(super)fn r110_controls(){{{nextmod}::r110_controls();}}\n')
f=ex/'r99_fold_check.rs';s=f.read_text();assert s.count('fn main(){')==1
save('r110_norm_check.rs',s.replace('fn main(){','fn main(){circle_norm::r110_controls();'))
f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r110-norm-check"\npath="../r110_norm_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r110_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r105_native']['fixtures'],'changed':len(set(changed))}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed))}))
