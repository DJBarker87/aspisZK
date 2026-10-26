"""Extract unchanged native wide operations through explicit proof entrypoints."""
from pathlib import Path
import os,subprocess,sys
r=Path(__file__).resolve().parents[3];d=Path(__file__).with_name('ports')
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--start-from','crate','--include','aspis_core::r0::scalar::_']
for x in ['aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::field::wide_exact::_::neg','aspis_core::field::wide_exact::_::new','aspis_core::field::wide_exact::_::c0','aspis_core::field::wide_exact::_::c1','aspis_core::field::wide_exact::_::U','aspis_core::field::wide_exact::canonical_qm31','aspis_core::field::ct::reduce64','aspis_core::field::ct::subtract_p']:
 cmd+=['--include',x]
if '--vectors' in sys.argv or '--empty' in sys.argv:
 a=cmd.index('--start-from');cmd[a+1]='crate::vec_default'
 cmd+=['--start-from','crate::vec_is_empty','--include','alloc::vec::_','--opaque','alloc::vec::Vec','--opaque','alloc::vec::_::new','--opaque','alloc::vec::_::len']
if '--empty' in sys.argv:cmd[cmd.index('--start-from')+1]='crate::vec_is_empty'
if '--compress' in sys.argv:
 cmd[cmd.index('--start-from')+1]='crate::compress'
 cmd+=['--opaque','aspis_statement','--include','aspis_statement::logup::compress_tagged_tuple','--include','aspis_statement::logup::lift']
cmd+=['--dest-file',str(r/('ProverRwSuccessCompress.llbc' if '--compress' in sys.argv else 'ProverRwSuccessEmpty.llbc' if '--empty' in sys.argv else 'ProverRwSuccessVectors.llbc' if '--vectors' in sys.argv else 'ProverRwSuccessPorts.llbc')),'--','--manifest-path',str(d/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
raise SystemExit(subprocess.run(cmd,cwd=r,env=dict(os.environ,CARGO_TARGET_DIR=str(r.parent/'charon-target'))).returncode)
