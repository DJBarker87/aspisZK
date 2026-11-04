"""One native slice-equality window with arbitrary accumulated invariant."""
import sys,json,subprocess
from NEU_native_patch import E,program
mode=sys.argv[1];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEU_prepare_window.py'),'1','positive'],check=True)
body='''use super::*;
#[kani::proof]
fn equality_step(){let left:[u8;1]=kani::any();let right:[u8;1]=kani::any();let before:bool=kani::any();let actual=before&&(left.as_slice()==right.as_slice());let expected=before&&(left[0]==right[0]);assert!(actual==@VALUE@);}
'''.replace('@VALUE@','!expected' if mode=='negative' else 'expected')
program(body,'NEU_equality_step')
(E/'NEU_EQUALITY_STEP_CURRENT.json').write_text(json.dumps(dict(mode=mode,domain='arbitrary live single-byte slices and arbitrary prior equality accumulator',classification='one actual native slice comparison; Lean prefix induction; association of the frozen688-byte compiler/library comparison to this iteration is still OPEN; no whole-buffer check'),indent=1)+'\n')
