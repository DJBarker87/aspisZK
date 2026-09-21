#!/usr/bin/env python3
"""Stage a 1024-point, first-479 G-prefix experiment without touching inputs."""
import argparse, hashlib, shutil, json
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS,one_replace

# Retained R24 fixed-size FFT endpoint, including R19 butterfly/R20 FMA
# and R23 hybrid numerator merges, NOT the older unoptimized tool template.
PIN = "2b9ded2a3c8330239bdb0ad581785750eab71c54b069ad7764661d7058c02698"
PREFIX_APPEND = r'''
// Experimental sparse-permutation correction prefix only.
// This is not the full G functional: callers must provide the exact geometric tail.
include!("r17_g_prefix_tables.rs");

pub(super) fn prefix_into(coins: &[K;271], out: &mut [K;1024]) {
    let mut work = vec![CM31::ZERO; 1024];
    numerator_into(coins, out, &mut work);
    out[271..].fill(K::ZERO);
    for component in 0..2 {
        for i in 0..1024 { work[i] = if component == 0 { out[i].c0 } else { out[i].c1 }; }
        fft(&mut work[..1024], false);
        for i in 0..1024 { work[i] = work[i].mul(PREFIX_INVERSE_SPECTRUM[i]); }
        fft(&mut work[..1024], true);
        for j in 0..479 { if component == 0 { out[j].c0 = work[j]; } else { out[j].c1 = work[j]; } }
    }
}

// Exact pivot helper for the lead's full geometric tail.  This is not a
// truncated G functional and is intentionally separate from prefix_into.
pub(super) fn pivot(coins: &[K;271]) -> K {
    let mut out = K::ZERO;
    for i in 0..271 { out = out.add(coins[i].mul_m31(M31(super::G_POWERS[1023][i]))); }
    out
}

#[cfg(not(performance_sbf))]
pub(super) fn check_fft1024() {
    let mut a=vec![CM31::ZERO;1024]; for (i,x) in a.iter_mut().enumerate() { *x=CM31::new(M31((17*i+3) as u32),M31((31*i+9) as u32)); }
    let original=a.clone(); fft(&mut a[..1024],false); fft(&mut a[..1024],true); assert_eq!(a,original);
    assert_eq!(ROOTS[2].pow(1024),CM31::ONE); assert_ne!(ROOTS[2].pow(512),CM31::ONE);
}
'''

ap = argparse.ArgumentParser(); ap.add_argument('--stage', type=Path, required=True); ap.add_argument('--output', type=Path, required=True)
a = ap.parse_args(); assert not a.output.exists()
control=json.loads((a.stage/'r17-compact-control.json').read_text())
predecessor=json.loads((a.stage/'r17-sbf-probe.json').read_text())
assert predecessor['fixed_fft']['r17_fast_g.rs']['after_sha256']==PIN
for name,expected in control['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==expected
for name,expected in control.get('core_files',{}).items():
    assert hashlib.sha256((a.stage/name).read_bytes()).hexdigest()==expected
shutil.copytree(a.stage, a.output)
exp = a.output / 'docs/research/v8-no-work-100-20260907/experiments'
src = exp / 'r17_fast_g.rs'; digest = hashlib.sha256(src.read_bytes()).hexdigest(); assert digest == PIN, (digest, PIN)
text = src.read_text()
needle = '        (2048,false) => fft_fixed::<2048,false>(a),'
if needle not in text: needle = '        (2048, false) => fft_fixed::<2048, false>(a),'
assert needle in text, 'R36 staged fast_g must expose fixed FFT dispatch'
replacement = needle.replace('(2048,false)', '(1024,false) => fft_fixed::<1024,false>(a),\n        (2048,false)').replace('(2048, false)', '(1024, false) => fft_fixed::<1024, false>(a),\n        (2048, false)')
text = text.replace(needle, replacement)
needle = '        (2048,true) => fft_fixed::<2048,true>(a),'
if needle not in text: needle = '        (2048, true) => fft_fixed::<2048, true>(a),'
assert needle in text, 'R36 staged fast_g must expose fixed FFT dispatch'
replacement = needle.replace('(2048,true)', '(1024,true) => fft_fixed::<1024,true>(a),\n        (2048,true)').replace('(2048, true)', '(1024, true) => fft_fixed::<1024, true>(a),\n        (2048, true)')
text = text.replace(needle, replacement)
tool = exp / 'r17_fast_g.rs'; tool.write_text(text + PREFIX_APPEND)
meta=json.loads((a.output/'r17-sbf-probe.json').read_text())
meta['g_prefix']={'r17_fast_g.rs':{'before_sha256':digest,'after_sha256':hashlib.sha256(tool.read_bytes()).hexdigest()}}
mask=exp/'r17_mask_workspace.rs';before=mask.read_bytes();source=before.decode()
start=source.index('    let mut scale = K::ONE;')
end=source.index('    fast_g::apply(coin_weights, weights);',start)
loop=source[start:end]
source+='''
// Same source coin loop, no new sampler or distribution.
pub(super) fn compact_prefix(point:&[K;ROUNDS],coin_weights:&mut[K;COINS],weights:&mut[K;N]) {
'''+loop+'''    fast_g::prefix_into(coin_weights,weights);
}
pub(super) fn compact_pivot(coins:&[K;COINS])->K {fast_g::pivot(coins)}
#[cfg(not(target_os="solana"))]
#[path="r17_g_prefix_control.rs"] mod prefix_control;
#[cfg(not(target_os="solana"))]
pub(super) fn check_prefix(){prefix_control::check();}
'''
mask.write_text(source)
meta['g_prefix'][mask.name]={'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':hashlib.sha256(mask.read_bytes()).hexdigest()}
shutil.copy2(Path(__file__).with_name('r17_g_prefix_generate.rs'), exp / 'r17_g_prefix_generate.rs')
shutil.copy2(Path(__file__).with_name('r17_g_prefix_control.rs'), exp / 'r17_g_prefix_control.rs')
manifest = exp / 'performance-host/Cargo.toml'
if manifest.exists() and 'r17-g-prefix-generate' not in manifest.read_text():
    manifest.write_text(manifest.read_text() + '\n[[bin]]\nname="r17-g-prefix-generate"\npath="../r17_g_prefix_generate.rs"\n')
(exp/'r17_g_prefix_check.rs').write_text('extern crate aspis_core as corelib;\nmod r17_structured_g;\nmod r17_mask_workspace;\nfn main(){r17_mask_workspace::check_prefix();}\n')
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-g-prefix-check"\npath="../r17_g_prefix_check.rs"\n')
meta['g_prefix_files']={name:hashlib.sha256((exp/name).read_bytes()).hexdigest() for name in ['r17_g_prefix_generate.rs','r17_g_prefix_control.rs','r17_g_prefix_check.rs']}
for name in list(meta['g_prefix'])+list(meta['g_prefix_files']):
    control['files'][name]=hashlib.sha256((exp/name).read_bytes()).hexdigest()
control['bin']='r17-g-prefix-check';control['scope']='479-coordinate prefix only; full tail and pivot separate'
(a.output/'r17-compact-control.json').write_text(json.dumps(control,indent=2)+'\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
print(f'PASS: staged new prefix module; pinned input r17_fast_g.rs sha256={digest}')
