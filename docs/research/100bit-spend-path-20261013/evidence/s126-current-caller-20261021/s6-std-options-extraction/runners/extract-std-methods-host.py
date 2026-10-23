#!/usr/bin/env python3
"""Focused actual Rust std method extraction for the complete codec's three ports."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-std-methods-extract-v1';phase=__import__('sys').argv[1];assert phase in ['charon','aeneas'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':
 P.mkdir(exist_ok=False);(P/'input').mkdir()
 (P/'input/Cargo.toml').write_text('[package]\nname="aspis-s6-std-methods"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[profile.release]\nopt-level=3\noverflow-checks=true\n')
 (P/'input/lib.rs').write_text("""pub fn option_ok_or<T,E>(value:Option<T>,error:E)->Result<T,E>{value.ok_or(error)}
pub fn option_eq<T:PartialEq>(a:&Option<T>,b:&Option<T>)->bool{a.eq(b)}
pub fn slice_array_eq<T:PartialEq<U>,U,const N:usize>(a:&[T],b:&[U;N])->bool{a.eq(b)}
""")
 T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
 patterns=['core::option::Option','core::result::Result','core::option::_::ok_or','core::option::_::eq','core::array::equality::_::eq','core::array::equality::_::spec_eq']
 cmd=[str(T),'cargo','--preset','aeneas','--mir','built','--sysroot','default',*sum((['--include',p] for p in patterns),[]),'--start-from','crate::option_ok_or','--start-from','crate::option_eq','--start-from','crate::slice_array_eq','--dest-file',str(P/'Std.llbc'),'--','--manifest-path',str(P/'input/Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 assert not json.loads((P/'Std.llbc').read_text())['has_errors'];T=H/'s6-formatter-tool-v5/source/src/_build/default/main.exe'
 cmd=[str(T),'-sequential','-no-progress-bar','-abort-on-error','-loops-no-rec','-backend','lean','-namespace','AspisS6StdMethods','-dest',str(P/'generated'),'-subdir','AspisS6StdMethods','-split-files','-emit-json',str(P/'Std.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s6-std-methods-'+phase+'-v1';collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
inv=json.loads(subprocess.check_output(['python3',str(collector)],text=True));(H/(tag+'-global-admission.json')).write_text(json.dumps(inv,indent=2)+'\n');assert inv['effective_sum_bytes']+2**30<=48*2**30 and inv['MemAvailable_kB']*1024>=3*2**30,'Global admission denied'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,tool_sha256=sha(T),source_sha256=sha(P/'input/lib.rs'),cargo_sha256=sha(P/'input/Cargo.toml'),llbc_sha256=sha(P/'Std.llbc') if phase=='aeneas' else None,qualification=__doc__,expected_time='Focused generic Rust std methods only; no codec/SDK rebuild or arithmetic evaluation. Explicit High512M/Max1G/Swap0.'),indent=2)+'\n')
os.chdir(P/'input');raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=512M','-p','MemoryMax=1G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused actual std methods extraction, generic complete carriers','--','timeout','120',*cmd]))
