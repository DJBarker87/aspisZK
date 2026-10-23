#!/usr/bin/env python3
"""Actual SDK stage1 through successful writeback/release, one byte projection.
The exact independently checked std-copy contract is used by stub_verified.
No SDK method model executes. Pure scan/comparison and typed child transport
remain explicit. This is the successor to the entry-only certificate.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);root=int(sys.argv[2]);args=sys.argv[3:]
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-entry.py'),str(O),str(root),*args],check=True)
p=O/'src/lib.rs';s=p.read_text();old=(R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-parent-cuts/sources/sdk-native-context-v9/src/lib.rs').read_text()
a=old.index(' static mut OBSERVED:');b=old.index('use aspis_s126_owned_sdk_snapshots',a);copy_helpers=old[a:b]
needle='#[derive(Clone,Copy)] struct EntryScalars';s=s.replace(needle,copy_helpers+'\n'+needle,1)
s=s.replace('candidate:[u8;688],k:usize,different:bool','candidate:[u8;688],output:[u8;1768],k:usize,different:bool')
s=s.replace('candidate:kani::any(),k:instruction[1] as usize','candidate:kani::any(),output:kani::any(),k:instruction[1] as usize')
needle=' kani::assume(false);\n Ok(Vec::new())';assert s.count(needle)==1;s=s.replace(needle,' Ok(plan().output.to_vec())')
s=s.replace(' kani::assume(false); // Return without first entry is outside this entry-precondition target.\n','')
s=s.replace(' assert!(actual.is_err());\n','')
s=s.replace('#[kani::stub(<[u8]>::copy_from_slice,unreachable_copy)]','#[kani::stub(<[u8]>::copy_from_slice,copy_bridge)]\n#[kani::stub_verified(verified_byte_copy)]')
needle=' let actual=native_prefix(&program,&accounts[..account_count],&instruction[..instruction_len]);';assert s.count(needle)==1
s=s.replace(needle,''' let copy_index:usize=if selected_root==2 {selected_index}else{0};
 unsafe{OBSERVED.value=copy_index;EXPECTED.value=plan().output[copy_index];}
'''+needle)
s='\n'.join(line for line in s.splitlines() if 'kani::cover!(true,"original SDK reaches checked first entry")' not in line and 'kani::cover!(unsafe{(*COUNTERS.value[0]).get()}==isize::MAX' not in line)+'\n'
needle=' // Native handles are gone.';assert s.count(needle)==1
pos=s.index(needle);s=s[:pos]+''' if actual.is_ok(){
  assert_eq!(unsafe{CALLS.value[0]},[1,1,1,1],"successful native source has the exact four-child order");
  if selected_root==2 {assert_eq!(buffers[2][selected_index],plan().output[selected_index],"native saved checkpoint equals SAME returned first output");}
  else {frame_probe();}
 } else {frame_probe();}
 kani::cover!(actual.is_ok(),"actual SDK source returns success after checkpoint write and Drop");
 kani::cover!(actual.is_ok()&&initial_counts[0]==isize::MAX-1,"successful native source with maximum permitted shared borrow count");
'''+s[pos:]
# Prepared Kani drops callback bodies used only by later C linking. Execute
# one fixture-only callback preflight, then reset every affected ghost before
# the unchanged native stage1. This retains the actual callback body.
needle=' let actual={';assert s.count(needle)==1
s=s.replace(needle,''' unsafe{CALLS.value[0]=[1,1,1,0];}
 let _=s126_coupled_cmp(pointers[0],pointers[0],688);
 unsafe{CALLS.value=[[0;4];2];CMP_CALLS.value=[0;2];}
'''+needle)
p.write_text(s)
p=O/'Cargo.toml';name='native-success-root'+str(root)+(f'-window{int(args[0])}' if root==0 else '')+'-v2';import re
p.write_text(re.sub(r'first-entry-root[012](?:-window\d+)?-v2',name,p.read_text()))
sha=lambda x:hashlib.sha256(x).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(s.encode()),copy_helpers_sha256=sha(copy_helpers.encode()),copy_owner_source_sha256=sha(old.encode()),copy_certificate='sdk-native-full-rc-copy-contract-v1; same helper/ghost source retained through native-context-v9; source-only parent packet',qualification=__doc__,callback_retention='One fixture-only direct call before native execution, with callback ghost fields restored afterward, prevents prepared Kani drop-unused from deleting the later C-linked callback body. No frozen input bytes or source body changed.',observer_root=root,observer_window=int(args[0]) if root==0 else None,remaining='All properties and covers must pass; checked copy contract requires exact source/ABI/ghost instantiation. Pure source scan/comparison and actual typed decoder/validator/encoder/first/oracle child installation, arbitrary valid runtime embedding and TX2 transport remain. This is not whole S2 or TOTAL source closure.'),indent=2)+'\n')
