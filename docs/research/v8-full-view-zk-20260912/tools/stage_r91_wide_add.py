#!/usr/bin/env python3
"""Bounded native add/sub widths; preserve raw-input overflow behavior."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True);p.add_argument('--outline-fallback',action='store_true')
p.add_argument('--add-only',action='store_true')
p.add_argument('--heap-recorder',action='store_true')
a=p.parse_args();src=a.control;dst=a.output
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='1d28d722eec96a50b6250c67ec3e80a14816acb457118e0adc340c756c8814ac'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='cc568c6d26d78d59dd0e2b113a2a8b52ee8628f6b0c276020f8766616f086e98'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
ref=ex/'r91_reference';ref.mkdir()
for name in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
    f=ref/name;shutil.copy2(src/'crates/aspis-core/src'/name,f);changed.append(f)
f=dst/'crates/aspis-core/src/field.rs';s=f.read_text()
old='''        let s = self.0 + rhs.0;
        M31(if s >= P { s - P } else { s })'''
new='''        let s = u64::from(self.0) + u64::from(rhs.0);
        if s > u64::from(u32::MAX) {
            // Preserve the original checked raw-constructor behavior.
            let old = self.0 + rhs.0;
            return M31(if old >= P { old - P } else { old });
        }
        M31(if s >= u64::from(P) { (s - u64::from(P)) as u32 } else { s as u32 })'''
assert s.count(old)==1;s=s.replace(old,new)
old='''        let s = self.0 + P - rhs.0;
        M31(if s >= P { s - P } else { s })'''
new='''        let top = u64::from(self.0) + u64::from(P);
        if top > u64::from(u32::MAX) || top < u64::from(rhs.0) {
            // Preserve both the original first-add overflow and subtraction
            // underflow; a later subtraction cannot hide the first failure.
            let old = self.0 + P - rhs.0;
            return M31(if old >= P { old - P } else { old });
        }
        let s = top - u64::from(rhs.0);
        M31(if s >= u64::from(P) { (s - u64::from(P)) as u32 } else { s as u32 })'''
assert s.count(old)==1;s=s.replace(old,old if a.add_only else new)
if a.outline_fallback:
    s=s.replace('''            let old = self.0 + rhs.0;
            return M31(if old >= P { old - P } else { old });''','''            return r91_raw_add(self,rhs);''')
    s=s.replace('''            let old = self.0 + P - rhs.0;
            return M31(if old >= P { old - P } else { old });''','''            return r91_raw_sub(self,rhs);''')
    s+='''
#[cold] #[inline(never)]
fn r91_raw_add(a:M31,b:M31)->M31 {let s=a.0+b.0;M31(if s>=P{s-P}else{s})}
#[cold] #[inline(never)]
fn r91_raw_sub(a:M31,b:M31)->M31 {let s=a.0+P-b.0;M31(if s>=P{s-P}else{s})}
'''
f.write_text(s);changed.append(f)
if a.heap_recorder:
    # Private trace construction only: retain its already allocated transitions
    # instead of copying two large fixed arrays onto the SBF stack.
    f=dst/'crates/aspis-statement/src/trace_v4.rs';s=f.read_text()
    edits=[
      ('#[derive(Clone, Copy, Debug, PartialEq, Eq)]\nstruct RecordedPermutation {',
       '#[derive(Clone, Debug, PartialEq, Eq)]\nstruct RecordedPermutation {'),
      ('    transitions: [Poseidon2RoundTransition; POSEIDON2_ROUNDS],',
       '    transitions: Vec<Poseidon2RoundTransition>,'),
      ('for (permutation, permutation_transitions) in transitions.iter().enumerate() {',
       'for (permutation, permutation_transitions) in transitions.into_iter().enumerate() {'),
      ('''            let round_array: [Poseidon2RoundTransition; POSEIDON2_ROUNDS] = permutation_transitions
                .as_slice()
                .try_into()
                .expect("instrumented permutation must emit 22 rounds");''',
       '''            assert_eq!(permutation_transitions.len(), POSEIDON2_ROUNDS,
                "instrumented permutation must emit 22 rounds");
            let round_array = permutation_transitions;'''),
      ('''            recorded.push(RecordedPermutation {
                pre_absorb,''',
       '''            let next_pre_absorb = round_array[POSEIDON2_ROUNDS - 1].output;
            recorded.push(RecordedPermutation {
                pre_absorb,'''),
      ('            pre_absorb = round_array[POSEIDON2_ROUNDS - 1].output;',
       '            pre_absorb = next_pre_absorb;')]
    for old,new in edits:
        assert s.count(old)==1,old;s=s.replace(old,new)
    f.write_text(s);changed.append(f)
f=ex/'r91_add_check.rs';shutil.copy2(Path(__file__).with_name(f.name),f);changed.append(f)
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r91-add-check"\npath="../r91_add_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r91_wide']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
    'public_raw_constructor_fallback_retained':True,'overflow_checks_enabled':True,
    'outlined_fallback':a.outline_fallback,'add_only':a.add_only,'heap_recorder':a.heap_recorder}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'modified_public_operations':['M31.add']if a.add_only else['M31.add','M31.sub']}))
