"""Replace unsupported DST contract shape by an equivalent fixed800 view.
Original module, weak function and harness names are intentionally retained.
"""
from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent;mode=sys.argv[1]
subprocess.run([sys.executable,str(E/'NEM_prepare_slice_contract.py'),mode],check=True)
p=E/'NEM_native_contracts.patch';text=p.read_text();head,rest=text.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_slice_contract.rs\n',1);body=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'))
assert body.count('out:&mut[u8],b:bool')==1
body=body.replace('out:&mut[u8],b:bool','out:&mut[u8;800],b:bool')
body=body.replace('let reply=weak(s,window,kani::any());','let array:&mut[u8;800]=window.try_into().unwrap();assert!(array.as_mut_ptr()==expected,"same fixed-array view place");let reply=weak(s,array,kani::any());')
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_slice_contract.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines()))
q=json.loads((E/'NEM_SLICE_CONTRACT_CURRENT.json').read_text());q.update(interface_shape='Result<(),PoolV1PairLiveSnapshotErrorV1>; immutable Snapshot; mutable [u8;800]; scalar Bool',replacement='NEM_K088 DST modifies control compiler ICE, no admission credit; fixed array view requires same pointer and universal Slice/Array800 poststate carrier theorem',names_retained=True)
(E/'NEM_ARRAY_CONTRACT_CURRENT.json').write_text(json.dumps(q,indent=1)+'\n')
