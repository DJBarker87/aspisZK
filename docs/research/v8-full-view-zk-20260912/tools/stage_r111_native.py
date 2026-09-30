#!/usr/bin/env python3
"""Fixed-offset decoder variant: remove R108's dynamic per-limb indexing."""
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
code=['// Fixed offsets over the SAME packed bytes; aligned interior only.',
 '#[inline(never)]','fn r55_decode_into<const N:usize>(bytes:&[u8],out:&mut[u32;N])->Result<(),Error>{',
 '    if N==0 || N%8!=0 || bytes.len()!=N/8*31{return Err(Error::Length);}',
 '    #[cfg(target_endian="little")] {',
 '        // u64 admits every bit pattern; no reads before/after this slice.',
 '        let (prefix,words,_)=unsafe{bytes.align_to::<u64>()};',
 '        match (N,prefix.len()) {']
for n in [104,48]:
    for prefix in range(8):code.append(f'            ({n},{prefix})=>return r111_{n}_{prefix}(bytes,words,out),')
code+=['            _=>(),','        }','    }','    r108_retained_decode(bytes,out)','}']
mapping_checks=0
for n in [104,48]:
    length=n*31//8
    for prefix in range(8):
        words=(length-prefix)//8;start=prefix*8;end=start+64*words
        code+=['#[cfg(target_endian="little")]','#[inline(never)]',
            f'fn r111_{n}_{prefix}<const N:usize>(bytes:&[u8],words:&[u64],out:&mut[u32;N])->Result<(),Error>{{',
            f'    if N!={n} || bytes.len()!={length} || words.len()!={words} {{return Err(Error::Length);}}',
            '    let mut invalid=0u32;']
        for i in range(n):
            bit=31*i
            if bit>=start and bit+31<=end:
                at=bit-start;w,shift=divmod(at,64);assert 0<=w<words
                expr=f'(words[{w}]>>{shift})'
                # Independent integer bit-origin check for every output bit.
                for b in range(31):
                    source=start+64*(w+(shift+b)//64)+(shift+b)%64
                    assert source==bit+b;mapping_checks+=1
                if shift>33:
                    assert w+1<words;expr+=f'|(words[{w+1}]<<{64-shift})'
            else:
                byte,shift=divmod(bit,8);count=(shift+31+7)//8;assert byte+count<=length
                expr='|'.join(f'(u64::from(bytes[{byte+j}])<<{8*j})'for j in range(count));expr=f'(({expr})>>{shift})'
                for b in range(31):assert 8*byte+shift+b==bit+b;mapping_checks+=1
            code.append(f'    let v=(({expr})&0x7fff_ffff)as u32;out[{i}]=v;invalid|=v+1;')
        code+=['    if invalid>>31==0{Ok(())}else{Err(Error::Canonical)}','}']
save('r111_decode.rs','\n'.join(code)+'\n')
f=ex/'query_arithmetic.rs';s=f.read_text();old='fn r55_decode_into<const N:usize>';assert s.count(old)==1
save(f.name,s.replace(old,'fn r108_retained_decode<const N:usize>')+'\ninclude!("r111_decode.rs");\ninclude!("r111_controls.rs");\n')
controls=(here/'r108_decode.rs').read_text();controls=controls[controls.index('#[cfg(not(v8_performance_sbf))]'):]
controls=controls.replace('r108_controls','r111_controls').replace('R108_DECODE','R111_DECODE')
needle='    let mut rng=0x108de_82749e82au64;';assert controls.count(needle)==1
controls=controls.replace(needle,'''    let mut bit_bases=0;
    for bit in 0..(152*31) {for offset in 0..8 {
        if bit<104*31 {let mut v=[0u32;104];v[bit/31]=1<<(bit%31);assert!(check(&v,offset));}
        else {let bit=bit-104*31;let mut v=[0u32;48];v[bit/31]=1<<(bit%31);assert!(check(&v,offset));}
        bit_bases+=1;
    }}
    println!("R111_BIT_BASIS comparisons={bit_bases} every_packed_bit=true offsets=8");
'''+needle)
save('r111_controls.rs',controls)
f=ex/'r55_opening_check.rs';s=f.read_text();assert s.count('fn main(){')==1
save('r111_decode_check.rs',s.replace('fn main(){','fn main(){query_arithmetic::r111_controls();'))
f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r111-decode-check"\npath="../r111_decode_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r111_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r105_native']['fixtures'],'changed':len(set(changed)),'bit_origin_checks':mapping_checks}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed)),'bit_origin_checks':mapping_checks}))
