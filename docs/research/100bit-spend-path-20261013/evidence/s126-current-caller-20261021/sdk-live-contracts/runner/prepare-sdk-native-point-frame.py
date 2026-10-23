#!/usr/bin/env python3
"""Pointwise native byte frame, avoiding per-byte DFCC shadow instrumentation.

One arbitrary original account allocation/index is observed before/after the
unchanged native decoder-error prefix. Quantification is over every byte,
not a chosen fixture value. A successful check still needs an extensional
composition theorem, scan transport and unrestricted runtime embedding.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-prefix-frame.py'),str(out)],check=True)
p=out/'src/lib.rs';s=p.read_text();s=s.replace('#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]','#[kani::proof] #[kani::unwind(48)]')
a=s.index('#[kani::modifies(');b=s.index('fn native_prefix(',a);s=s[:a]+s[b:]
needle=' let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());'
assert s.count(needle)==1
s=s.replace(needle,needle+'''
 let selected_root:usize=kani::any();kani::assume(selected_root<3);
 let selected_index:usize=kani::any();kani::assume(selected_index<buffers[selected_root].len());
 let original_byte=buffers[selected_root][selected_index];
 let lengths=core::array::from_fn::<_,3,_>(|i|buffers[i].len());
 let capacities=core::array::from_fn::<_,3,_>(|i|buffers[i].capacity());
''')
needle=' assert_eq!(amounts,initial_amounts);'
assert s.count(needle)==1
s=s.replace(needle,needle+'''
 assert_eq!(buffers[selected_root][selected_index],original_byte,"arbitrary native-prefix account byte preserved");
 for i in 0..3 {
  assert_eq!(buffers[i].as_ptr(),pointers[i]);
  assert_eq!(buffers[i].len(),lengths[i]);
  assert_eq!(buffers[i].capacity(),capacities[i]);
 }
''')
p.write_text(s)
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,point_frame='Symbolic root0..2 and every valid index in its original allocation, no byte values constrained. All buffer Vec addresses/lengths/capacities, scalar Rc/counter/lamport fields checked. No DFCC contract assumed or enforced; these are actual before/after assertions. Full frame requires extensional composition across all index choices on the same unchanged native execution.')
p.write_text(json.dumps(m,indent=2)+'\n')
