#!/usr/bin/env python3
"""Exact checked-u32 semantics with widened temporaries, isolated experiment."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--cold-fallback',action='store_true');a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==(183 if 'r24_qm' in m else 182)
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';text=field.read_text()
for old,new in [
('''let s = self.0 + rhs.0;
        M31(if s >= P { s - P } else { s })''','''let s = u64::from(self.0) + u64::from(rhs.0);
        if s > u64::from(u32::MAX) {
            // Preserve the original operation (and its checked overflow).
            let old = self.0 + rhs.0;
            return M31(if old >= P { old - P } else { old });
        }
        M31((if s >= u64::from(P) { s - u64::from(P) } else { s }) as u32)'''),
('''let s = self.0 + P - rhs.0;
        M31(if s >= P { s - P } else { s })''','''let left = u64::from(self.0) + u64::from(P);
        if left > u64::from(u32::MAX) || left < u64::from(rhs.0) {
            // Same first-add overflow / subsequent-sub underflow behavior.
            let old = self.0 + P - rhs.0;
            return M31(if old >= P { old - P } else { old });
        }
        let s = left - u64::from(rhs.0);
        M31((if s >= u64::from(P) { s - u64::from(P) } else { s }) as u32)''')]:
    assert text.count(old)==1;text=text.replace(old,new)
if a.cold_fallback:
    for old,new in [('''let old = self.0 + rhs.0;
            return M31(if old >= P { old - P } else { old });''','return r24_add_fallback(self.0,rhs.0);'),('''let old = self.0 + P - rhs.0;
            return M31(if old >= P { old - P } else { old });''','return r24_sub_fallback(self.0,rhs.0);')]:
        assert text.count(old)==1;text=text.replace(old,new)
    text+='''
#[cold] #[inline(never)] fn r24_add_fallback(a:u32,b:u32)->M31 {
    let s=a+b; M31(if s>=P{s-P}else{s})
}
#[cold] #[inline(never)] fn r24_sub_fallback(a:u32,b:u32)->M31 {
    let s=a+P-b; M31(if s>=P{s-P}else{s})
}
'''
field.write_text(text)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';test=ex/'r23_field_check.rs';text=test.read_text();at='    std::panic::set_hook(hook);'
extra='''    let raw=[0,1,P-1,P,P+1,u32::MAX/2+2,u32::MAX-1,u32::MAX];
    for x in raw {for y in raw {
        for sub in [false,true] {
            let original=std::panic::catch_unwind(|| {
                let (a,b)=(r23_reference_field::M31(std::hint::black_box(x)),r23_reference_field::M31(std::hint::black_box(y)));
                if sub {a.sub(b).0}else{a.add(b).0}
            });
            let actual=std::panic::catch_unwind(|| {
                let (a,b)=(M31(std::hint::black_box(x)),M31(std::hint::black_box(y)));
                if sub {a.sub(b).0}else{a.add(b).0}
            });
            match (original,actual) {(Ok(x),Ok(y))=>assert_eq!(x,y),(Err(_),Err(_))=>(),_=>panic!("raw add/sub outcome changed")}
        }
    }}
    println!("R24_ADDSUB raw_boundary_cases=128 original_panic_behavior_retained=true");
'''
assert text.count(at)==1;test.write_text(text.replace(at,extra+at))
for path in [field,test]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_addsub']={'control_manifest_sha256':sha(src/'r18-stage.json'),'sites':2,'checked_panic_fallback_retained':True,'cold_fallback':a.cold_fallback}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
