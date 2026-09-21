#!/usr/bin/env python3
"""Specialize public FFT lengths/directions and exact quarter-turn butterflies."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS, one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
meta=json.loads((a.output/'r17-sbf-probe.json').read_text())
path=root/'r17_fast_g.rs'
before=path.read_bytes()
assert hashlib.sha256(before).hexdigest()==meta['hybrid_merge'][path.name]['after_sha256']
s=before.decode()
start=s.index('pub(super) fn fft(')
end=s.index('\n// Both numerator buffers',start)
old=s[start:end]
new=one_replace(old,'''pub(super) fn fft(a: &mut [CM31], inverse: bool) {
    let n = a.len();
    assert!(matches!(n,64|128|256|2048));''','''fn fft_fixed<const N: usize, const INVERSE: bool>(a: &mut [CM31]) {
    let n = N;
    assert_eq!(a.len(),N);''','compile-time public schedule')
new=new.replace('if inverse','if INVERSE')
new=one_replace(new,'''                let (plus, minus) = if index == 0 { (u.add(v), u.sub(v)) }
                    else { butterfly(u, v, ROOTS[index]) };''','''                let (plus, minus) = if index == 0 { (u.add(v), u.sub(v)) }
                    else if index == 512 || index == 1536 { quarter_turn(u,v,INVERSE) }
                    else { butterfly(u, v, ROOTS[index]) };''','public quarter-turn special case')
wrapper='''#[inline(always)]
fn quarter_turn(u: CM31, v: CM31, inverse: bool) -> (CM31,CM31) {
    // ROOTS[512]=-i, ROOTS[1536]=i. No limb multiplication or negation.
    let plus=CM31::new(u.a.add(v.b),u.b.sub(v.a));
    let minus=CM31::new(u.a.sub(v.b),u.b.add(v.a));
    if inverse {(minus,plus)} else {(plus,minus)}
}

pub(super) fn fft(a: &mut [CM31], inverse: bool) {
    match (a.len(),inverse) {
'''
for n in [64,128,256,2048]:
    for direction in ['false','true']:
        wrapper+=f'        ({n},{direction}) => fft_fixed::<{n},{direction}>(a),\n'
wrapper+='        _ => panic!("unsupported public FFT length"),\n    }\n}\n\n'
s=s[:start]+wrapper+new+s[end:]
s+='\n#[cfg(not(performance_sbf))]\n'+old.replace('pub(super) fn fft(', 'fn fft_reference(')
s+='''
#[cfg(not(performance_sbf))]
fn check_fixed_fft() {
    assert_eq!(ROOTS[512],CM31::new(M31::ZERO,M31(2147483646)));
    assert_eq!(ROOTS[1536],CM31::new(M31::ZERO,M31::ONE));
    let limbs=[0u32,1,2,2147483645,2147483646];
    for code in 0..625usize {
        let mut n=code;let mut z=[0;4];
        for x in &mut z {*x=limbs[n%5];n/=5;}
        let u=CM31::new(M31(z[0]),M31(z[1]));let v=CM31::new(M31(z[2]),M31(z[3]));
        for (inverse,index) in [(false,512),(true,1536)] {
            let p=v.mul(ROOTS[index]);
            assert_eq!(quarter_turn(u,v,inverse),(u.add(p),u.sub(p)));
        }
    }
    for n in [64usize,128,256,2048] {
        for inverse in [false,true] {
            for case in 0..5 {
                let mut actual:Vec<_>=(0..n).map(|i| match case {
                    0=>CM31::ZERO,
                    1=>CM31::new(M31(2147483646),M31(2147483646)),
                    2=>if i==n-1 {CM31::new(M31(3),M31(7))} else {CM31::ZERO},
                    3=>CM31::new(M31((i*17+9) as u32),M31((i*93+3) as u32)),
                    _=>CM31::new(M31::reduce_u64(i as u64*0x9e3779b9),M31::reduce_u64(i as u64*0x85ebca6b+71))
                }).collect();
                let mut expected=actual.clone();
                fft(&mut actual,inverse);fft_reference(&mut expected,inverse);
                assert_eq!(actual,expected,"n {n}, inverse {inverse}, case {case}");
            }
        }
    }
    println!("PASS: 1250 quarter-turn boundary controls and 40 fixed-size/direction FFTs equal retained generic transform");
}
'''
s=one_replace(s,'pub(super) fn check() {','pub(super) fn check() {\n    check_fixed_fft();','specialization gate')
path.write_text(s)
meta['fixed_fft']={path.name:{'before_sha256':hashlib.sha256(before).hexdigest(),
    'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}}
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
