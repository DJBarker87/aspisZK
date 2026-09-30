#!/usr/bin/env python3
"""Two isolated same-proof native experiments, each with a pinned control."""
import argparse,ast,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--variant',choices=['aligned','inactive'],required=True);p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=={'aligned':'da13eae6f166b41cc70c14801345f9234d317f91aa8b01a57eddd550692e7e22','inactive':'87f8c0748b21cd11000f5352d29de588192942354b1e11def7801d7a399b2eee'}[a.variant]
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
if a.variant=='aligned':
    f=ex/'r103_words.rs';s=f.read_text();anchor='    let mut invalid=0u32;\n';assert s.count(anchor)==1
    fast='''    // align_to checks BOTH alignment and exact coverage; arbitrary bytes
    // are valid u32 representations. No typed reference to unaligned memory.
    // Big-endian and misaligned inputs retain the byte-decoding path.
    #[cfg(target_endian="little")]
    {
        let (prefix,words,suffix)=unsafe {bytes.align_to::<u32>()};
        if prefix.is_empty() && suffix.is_empty() {
            let mut invalid=0u32;
            for (dst,&v) in out.iter_mut().zip(words) {
                *dst=v;invalid|=v|v.wrapping_add(1);
            }
            return if invalid>>31!=0{Err(Error::Canonical)}else{Ok(())};
        }
    }
'''
    s=s.replace(anchor,fast+anchor)
    anchor='        let a=&words[..416];let b=&words[416..];';assert s.count(anchor)==1
    s=s.replace(anchor,anchor+'''
        for offset in 0..4 {
            let mut unaligned=vec![0;offset];unaligned.extend_from_slice(&words);
            let mut actual=[0;152];decode(&unaligned[offset..],&mut actual).unwrap();
            assert_eq!(actual,values);
        }''')
    save('r103_words.rs',s)
else:
    f=ex/'r22_scalar.rs';s=f.read_text();start=s.index('    const MASKS:');end=s.index('    #[cfg(not(target_os="solana"))]',start)
    tables=s[start:end];consts={}
    for name in ['MASKS','IDS','ENDS','ROWS']:
        consts[name]=ast.literal_eval(re.search(r'const '+name+r':[^=]+=(\[[^;]+\]);',tables)[1])
    assert 'false'not in re.search(r'const COMPLEMENT:[^=]+=(\[[^;]+\]);',tables)[1]
    masks,ids,ends,rows=[consts[n]for n in ['MASKS','IDS','ENDS','ROWS']]
    for low in range(16):
        subset=rows[ends[ids[low]]:ends[ids[low]+1]]
        assert len(set(subset))==len(subset)and all(0<=j<64 for j in subset)
        assert (1<<64)-1-sum(1<<j for j in subset)==masks[low]
    save('r104_inactive.rs',tables+(here/'r104_inactive.rs').read_text())
    old='fn r24_inactive_values(hb:&[K],values:&mut[K;19]) {';assert s.count(old)==1
    s=s.replace(old,'''fn r24_inactive_values(hb:&[K],values:&mut[K;19]) {
    if r104_inactive::values(hb,values) {
        #[cfg(not(target_os="solana"))] {
            let mut reference=[K::ZERO;19];r104_retained_inactive(hb,&mut reference);
            assert_eq!(*values,reference);
        }
        return;
    }
    r104_retained_inactive(hb,values)
}
#[path="r104_inactive.rs"] mod r104_inactive;
#[inline(never)]
fn r104_retained_inactive(hb:&[K],values:&mut[K;19]) {''')
    save('r22_scalar.rs',s)
    save('r104_sum_check.rs','extern crate aspis_core as corelib;\nmod r104_inactive;\nfn main(){r104_inactive::controls();}\n')
    f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r104-sum-check"\npath="../r104_sum_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r104_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),'variant':a.variant,
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':[{'path':str(src/f'r24-host-a/fixture-world{w}'),'sha256':sha(src/f'r24-host-a/fixture-world{w}/proof-1.bin')}for w in range(2)],'changed':len(set(changed))}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed)),'variant':a.variant}))
