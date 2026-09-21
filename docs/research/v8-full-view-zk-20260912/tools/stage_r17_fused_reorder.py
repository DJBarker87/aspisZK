#!/usr/bin/env python3
"""Keep fast DIT butterflies; absorb reordering into loads and spectral products."""
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
assert 'aligned_fft' not in meta, 'derive from retained R24, not rejected DIF experiment'
changes={}
path=root/'r17_fast_g.rs';before=path.read_bytes()
assert hashlib.sha256(before).hexdigest()==meta['fixed_fft'][path.name]['after_sha256']
s=before.decode()
start=s.index('pub(super) fn fft(');end=s.index('\n// Both numerator buffers',start)
loaded=s[start:end].replace('fn fft(', 'fn fft_loaded(').replace('fft_fixed','fft_loaded_fixed')
loaded=one_replace(loaded,'''    let mut j = 0;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 { j ^= bit; bit >>= 1; }
        j ^= bit;
        if i < j { a.swap(i, j); }
    }
''','', 'caller already supplies bit-reversed input')
s+='''
const fn make_reversed_indices() -> [usize;2048] {
    let mut out=[0;2048];let mut i=0usize;
    while i<2048 {out[i]=i.reverse_bits()>>(usize::BITS-11);i+=1;}
    out
}
static REVERSED_INDICES:[usize;2048]=make_reversed_indices();
#[inline(always)]
fn reversed(i:usize,n:usize)->usize {REVERSED_INDICES[i]>>(11-n.trailing_zeros())}
'''+loaded
start=s.index('pub(super) fn apply(');end=s.index('\n#[cfg',start)
part=s[start:end]
part=one_replace(part,'work[i] = if component', 'work[reversed(i,2048)] = if component','scatter source coefficients')
part=part.replace('fft(&mut work,','fft_loaded(&mut work,')
part=one_replace(part,'''        for i in 0..2048 { work[i] = work[i].mul(INVERSE_SPECTRUM[i]); }''','''        // Each public pair is read completely before either output is written.
        for i in 0..2048 {
            let j=reversed(i,2048);
            if i<=j {
                let a=work[i].mul(INVERSE_SPECTRUM[i]);
                if i==j {work[i]=a;} else {
                    let b=work[j].mul(INVERSE_SPECTRUM[j]);
                    work[i]=b;work[j]=a;
                }
            }
        }''','fuse pointwise product and inverse input ordering')
s=s[:start]+part+s[end:]
s+='''
#[cfg(not(performance_sbf))]
fn check_fused_reorder() {
    for n in [64usize,128,256,2048] {
        for i in 0..n {
            assert_eq!(reversed(i,n),i.reverse_bits()>>(usize::BITS-n.trailing_zeros()));
            assert!(reversed(i,n)<n);assert_eq!(reversed(reversed(i,n),n),i);
        }
        for inverse in [false,true] {
            for case in 0..5 {
                let input:Vec<_>=(0..n).map(|i|match case {
                    0=>CM31::ZERO,
                    1=>CM31::new(M31(2147483646),M31(2147483646)),
                    2=>if i==n-1 {CM31::new(M31(3),M31(7))} else {CM31::ZERO},
                    3=>CM31::new(M31((i*17+9) as u32),M31((i*93+3) as u32)),
                    _=>CM31::new(M31::reduce_u64(i as u64*0x9e3779b9),M31::reduce_u64(i as u64*0x85ebca6b+71))
                }).collect();
                let mut expected=input.clone();fft(&mut expected,inverse);
                let mut actual:Vec<_>=(0..n).map(|i|input[reversed(i,n)]).collect();
                fft_loaded(&mut actual,inverse);assert_eq!(actual,expected);
            }
        }
    }
    println!("PASS: all supported reversal indices in range/involutive and 40 preordered DIT transforms equal retained FFT");
}
'''
s=one_replace(s,'pub(super) fn check() {','pub(super) fn check() {\n    check_fused_reorder();','new schedule controls')
path.write_text(s)
changes[path.name]={'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
path=root/'r17_hybrid_merge.rs';before=path.read_bytes()
assert hashlib.sha256(before).hexdigest()==meta['hybrid_merge_files'][path.name]
s=before.decode()
runtime,host=s.split('#[cfg(not(performance_sbf))]',1)
runtime=runtime.replace('left[i] = if component','left[reversed(i,n)] = if component').replace('right[i] = if component','right[reversed(i,n)] = if component')
runtime=runtime.replace('fft(left,','fft_loaded(left,').replace('fft(right,','fft_loaded(right,')
runtime=one_replace(runtime,'''        for i in 0..n {
            left[i] = left[i].mul(MERGE_SPECTRA[offset+i])
                .add(right[i].mul(MERGE_SPECTRA[offset+n+i]));
        }''','''        for i in 0..n {
            let j=reversed(i,n);
            if i<=j {
                let a=left[i].mul(MERGE_SPECTRA[offset+i]).add(right[i].mul(MERGE_SPECTRA[offset+n+i]));
                if i==j {left[i]=a;} else {
                    let b=left[j].mul(MERGE_SPECTRA[offset+j]).add(right[j].mul(MERGE_SPECTRA[offset+n+j]));
                    left[i]=b;left[j]=a;
                }
            }
        }''','fused two-product sum and inverse input ordering')
path.write_text(runtime+'#[cfg(not(performance_sbf))]'+host)
changes[path.name]={'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
meta['fused_reorder']=changes
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
