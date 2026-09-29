#!/usr/bin/env python3
"""Persistent private packed representation; same R87 arithmetic/wire/profile."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='ddece23bc284c96ef9fc1d2e973701af7c2fdb347529941cd2bf7daf911c749a'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='95fbbdf3ed3acb9bd8fda2e8a130bad22e1ae14b58d9147f45044ef24ab3df94'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
f=ex/'r81_canonical_basis.rs';s=f.read_text()
assert s.count('pub struct Q([u32;4]);')==1
s=s.replace('pub struct Q([u32;4]);','pub struct Q([u64;2]);')
start=s.index('    pub const ZERO:Self=');end=s.index('    pub fn half_pow',start)
s=s[:start]+'''    pub const ZERO:Self=Self([0;2]);pub const ONE:Self=Self([1,0]);
    #[inline(always)] fn pack(x:[u32;4])->Self {Self([pair(x[0],x[1]),pair(x[2],x[3])])}
    pub fn from_limbs(x:[u32;4])->Option<Self>{if x.iter().all(|&v|v<P){Some(Self::pack(x))}else{None}}
    pub fn from_m31(x:u32)->Option<Self>{if x<P{Some(Self([u64::from(x),0]))}else{None}}
    pub const fn limbs(self)->[u32;4]{[self.0[0] as u32,(self.0[0]>>32) as u32,self.0[1] as u32,(self.0[1]>>32) as u32]}
    #[inline(always)] pub fn add(self,rhs:Self)->Self {
        Self([reduce_pair(self.0[0].wrapping_add(rhs.0[0])),reduce_pair(self.0[1].wrapping_add(rhs.0[1]))])
    }
    #[inline(always)] pub fn sub(self,rhs:Self)->Self {
        Self([reduce_pair(self.0[0].wrapping_add(MASK).wrapping_sub(rhs.0[0])),
            reduce_pair(self.0[1].wrapping_add(MASK).wrapping_sub(rhs.0[1]))])
    }
    #[inline(always)] pub fn half(self)->Self {
        // Clear the cross-lane bit in the spare bit-31 position after
        // shifting; rotate each original odd bit to its lane's bit 30.
        let h=|v:u64|((v>>1)&MASK)|((v&ONES)<<30);Self(self.0.map(h))
    }
'''+s[end:]
start=s.index('    pub fn half_pow');s=s[:start]+s[start:].replace('self.0.map','self.limbs().map').replace('rhs.0.map','rhs.limbs().map').replace('Self(self.limbs().map','Self::pack(self.limbs().map').replace('Self([reduce(','Self::pack([reduce(').replace('Self(sums.map(reduce))','Self::pack(sums.map(reduce))')
assert 'self.0' not in s[s.index('    pub fn half_pow'):]
s+='\nconst _:()={assert!(core::mem::size_of::<Q>()==16);};\n'
f.write_text(s);changed.append(f)
f=ex/'r20_semantic_basis.rs';s=f.read_text()
needle='(x.sub(y),old(a).sub(old(b)))]'
assert s.count(needle)==1
s=s.replace(needle,'''(x.sub(y),old(a).sub(old(b))),
            (x.half(),old(a).half()),(x.square(),old(a).square()),
            (Q::dot([x,y],[y,x]),old(a).mul(old(b)).add(old(b).mul(old(a))))]''')
s=s.replace('operation_comparisons=796608','operation_comparisons=1593216')
f.write_text(s);changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r89_packed']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
    'private_representation':'two canonical 31-bit lanes per u64; two words per Q',
    'public_field_and_decoder_unchanged':True,'all_entry_guards_retained':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'private_packed_words':2}))
