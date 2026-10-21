#!/usr/bin/env python3
"""Full SDK descriptor/counter join across every input length0..58295.
The actual owned-reference functions and complete owned state are retained.
Byte-content clone/identity is separately TOTAL in Lean; this gate checks
slice/Vec descriptor frames and counters, not whole-stage or byte-copy equality.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
O=Path(sys.argv[1]);kit=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(kit/'prepare-sdk-owned-borrow-join.py'),str(O),'shared'],check=True)
p=O/'src/lib.rs';s=p.read_text().replace('1768','58295')
s=s.replace('let selected:usize=kani::any();kani::assume(selected<58295);','let length:usize=kani::any();kani::assume(length<=58295);')
s=s.replace('let snapshot=bytes.to_vec();let initial_byte=bytes[selected];','let input_ptr=bytes.as_ptr();let snapshot=bytes[..length].to_vec();let model_ptr=snapshot.as_ptr();')
s=s.replace('&mut bytes,&owner','&mut bytes[..length],&owner')
s=s.replace('assert_eq!(model.data_cells[0].bytes[selected],guard[selected]);','assert_eq!(guard.as_ptr(),input_ptr);assert_eq!(guard.len(),length);\n    assert_eq!(model.data_cells[0].bytes.as_ptr(),model_ptr);assert_eq!(model.data_cells[0].bytes.len(),length);')
s=s.replace('assert_eq!(model.data_cells[0].bytes[selected],initial_byte);','assert_eq!(model.data_cells[0].bytes.as_ptr(),model_ptr);assert_eq!(model.data_cells[0].bytes.len(),length);')
s=s.replace('kani::cover!(initial==isize::MAX,"matching saturated failure");','kani::cover!(initial==0 && length==58295,"complete proof-length descriptor");\n  kani::cover!(initial==0 && length==0,"empty descriptor");\n  kani::cover!(initial==isize::MAX,"matching saturated failure");')
assert 'selected' not in s
if len(sys.argv)>2 and sys.argv[2]=='byte-frame':
 s=s.replace('let input_ptr=bytes.as_ptr();', 'let selected:usize=kani::any();kani::assume(length==0 || selected<length);let initial_byte=if length==0 {0} else {bytes[selected]};\n  let input_ptr=bytes.as_ptr();')
 s=s.replace('assert_eq!(guard.as_ptr(),input_ptr);', 'assert_eq!(guard.as_ptr(),input_ptr);if length>0 {assert_eq!(guard[selected],initial_byte);}')
p.write_text(s)
cut=json.loads((O/'source-cut.json').read_text());cut['byte_frame']=len(sys.argv)>2 and sys.argv[2]=='byte-frame';cut.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,domain='All signed counters, all metadata/lamports and arbitrary full58295-byte storage, symbolic view length0..58295. Descriptor/counter frames only; arbitrary-byte clone identity supplied by separately checked concrete Lean theorem, not assumed whole-source correspondence.')
(O/'source-cut.json').write_text(json.dumps(cut,indent=2)+'\n')
