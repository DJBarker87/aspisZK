#!/usr/bin/env python3
"""Actual typed guard drop_in_place frame; no by-value verified-stub cleanup.
The real SDK supplies the actual guard. ManuallyDrop only suppresses a second
fixture destruction. No SDK/Drop model or stub in the selected leaf proof.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);mode=sys.argv[2];assert mode in ['shared','exclusive'];assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-drop-frame.py'),str(O),mode],check=True)
p=O/'src/lib.rs';s=p.read_text();kind='Ref' if mode=='shared' else 'RefMut'
s=s.replace('std::mem::size_of_val(&guard)','std::mem::size_of_val(unsafe{&*guard})')
s=s.replace('std::ptr::addr_of!(guard).cast::<usize>()','guard.cast::<usize>()')
s=s.replace(f"fn finish_guard(guard:std::cell::{kind}<'_,&mut [u8]>,counter:*const Cell<isize>){{drop(guard);}}",f"fn finish_guard(guard:*mut std::cell::{kind}<'_,&mut [u8]>,counter:*const Cell<isize>){{unsafe{{std::ptr::drop_in_place(guard);}}}}")
needle='Ok(guard)=>finish_guard(guard,counter)';assert s.count(needle)==1
s=s.replace(needle,'Ok(guard)=>{let mut guard=std::mem::ManuallyDrop::new(guard);finish_guard(&mut *guard,counter)}')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace(f'sdk-drop-{mode}-v1',f'sdk-raw-drop-{mode}-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,mode=mode,remaining='Leaf must pass and then actual caller supplies valid guard pointer, counter word and live count. Compiler cleanup/explicit typed calls, source scope, runtime heap/ABI and full native/reference/oracle/TX2 composition remain.'),indent=2)+'\n')
