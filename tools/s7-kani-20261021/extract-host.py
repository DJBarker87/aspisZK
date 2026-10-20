#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];O=R/'extraction';O.mkdir(exist_ok=True)
C=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
pins={str(C):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',str(C.with_name('charon-driver')):'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45',str(A):'4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'}
for p,h in pins.items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h
(O/'tool-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
phase=sys.argv[1]
if phase=='charon':
 cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
 for path in ['core::option::Option','core::result::Result','core::result::_::map_err']:cmd+=['--include',path]
 for path in ['accumulate_owned','accumulate_optional_owned','query_owned','query_loop_owned','geometry_owned']:cmd+=['--start-from','crate::'+path]
 for path in ['aspis_core','crate::fast_domain','crate::fast_dots','crate::fast_pairing','crate::trace']:cmd+=['--opaque',path]
 for path in ['r0::domain::Point','circle::SecureCirclePoint','field::M31','field::CM31','field::QM31','field::wide_exact::WideExact']:cmd+=['--include','aspis_core::'+path]
 cmd+=['--dest-file',str(O/'S7Owned.llbc'),'--','--manifest-path',str(R/'tools/s7-kani-20261021/Cargo.toml'),'--offline','--release','--lib','--jobs','4']
else:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','S7OwnedP6','-dest',str(O/'generated'),'-subdir','S7OwnedP6','-split-files','-emit-json',str(O/'S7Owned.llbc')]
(O/(phase+'-command.json')).write_text(json.dumps(cmd,indent=2)+'\n')
raise SystemExit(subprocess.call(cmd,cwd=R))
