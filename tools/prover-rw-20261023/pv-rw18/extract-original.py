"""Probe the original frozen helper at optimized MIR; never rewrites Rust.

The earlier built-MIR loop failed in Aeneas collapse_ctx_following_sequence.
This is a different frontend input, not a retry of that failed LLBC. No op223
callback source law is installed here; pv-cb3 retains that ownership.
"""
from pathlib import Path
import subprocess,os,sys
r=Path(__file__).resolve().parents[3]
mono='--mono' in sys.argv
mono_mut='--mono-mut' in sys.argv
precise='--precise' in sys.argv
entry='crate::logup::lift' if '--lift' in sys.argv else 'crate::logup::compress_tagged_tuple'
name='ProverRw18Lift' if '--lift' in sys.argv else ('ProverRw18OriginalMut' if mono_mut else ('ProverRw18OriginalPrecise' if precise else ('ProverRw18OriginalMono' if mono else 'ProverRw18OriginalOptimized')))
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon',
 'cargo','--preset','aeneas','--mir','optimized','--sysroot','default',
 '--opaque','aspis_core','--start-from',entry]
if mono:cmd+=['--monomorphize']
if mono_mut:cmd+=['--monomorphize-mut=all']
if precise:cmd+=['--precise-drops','--desugar-drops']
for x in ['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31']:
 cmd+=['--include',x]
cmd+=['--dest-file',str(r/(name+'.llbc')),'--',
 '--manifest-path',str(r/'crates/aspis-statement/Cargo.toml'),'--release','--offline',
 '--features','r0,aspis-core/ct-host-prover','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
