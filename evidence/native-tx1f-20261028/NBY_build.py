from pathlib import Path
import sys,json,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBY_host as h
attrs='''#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
text='use super::*;\n'
cases=[]
def pair(name,body,expr,scope='candidate'):
 global text
 for neg in [False,True]:
  n=name+('_wrong' if neg else '')
  text+=attrs+'fn '+n+'(){'+body+('assert!(!('+expr+'));' if neg else 'assert!('+expr+');')+'}\n'
  cases.append((n,scope,neg))
pair('NBY_reborrow_load','let a:[u8;32]=kani::any();let start:usize=kani::any();let len:usize=kani::any();let k:usize=kani::any();kani::assume(start<=32&&len<=32-start&&k<len);let q=&a[start..start+len];let p=q.as_ptr();let x=q[k];', 'x==a[start+k]&&p==a.as_ptr().wrapping_add(start)')
pair('NBY_reborrow_nested','let a:[u8;32]=kani::any();let start:usize=kani::any();let end:usize=kani::any();let offset:usize=kani::any();let k:usize=kani::any();kani::assume(start<=end&&end<=32&&offset<=end-start&&k<end-start-offset);let q=&a[start..end];let r=&q[offset..];', 'r[k]==a[start+offset+k]&&r.len()==end-start-offset')
pair('NBY_reborrow_read_frame','let a:[u8;32]=kani::any();let j:usize=kani::any();let k:usize=kani::any();let begin:usize=kani::any();kani::assume(begin<32&&j<32-begin&&k<32);let before=a[k];let q=&a[begin..];let read=q[j];', 'a[k]==before&&read==a[begin+j]')
pair('NBY_load8','let a:[u8;32]=kani::any();let start:usize=kani::any();let k:usize=kani::any();kani::assume(start<=24&&k<8);let q=&a[start..start+8];', 'q[k]==a[start+k]')
files={'crates/aspis-r1-cost-probe/src/NBY_opening.rs':text}
# Start from frozen sources plus inherited read-only modules, never write their owners.
r=h.remote_py(f'from pathlib import Path\np=Path({(h.B+"/NBY_src/crates/aspis-r1-cost-probe/src/candidate.rs")!r})\nprint(p.read_text(),end="")');assert r.returncode==0,r.stderr
files['crates/aspis-r1-cost-probe/src/candidate.rs']=r.stdout+'\n#[cfg(kani)]\n#[path="NBY_opening.rs"]\nmod NBY_opening;\n'
h.admit('NBY_UPLOAD1')
r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBY_src"/n).write_text(s)');assert r.returncode==0,r.stderr
patch=''
for n,s in files.items():
 old=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NBY_opening.patch').write_text(patch)
base=json.loads((R/'evidence/native-tx1e-20261028/NBV_K050.json').read_text())
for num,(name,scope,neg) in enumerate(cases,1):
 a=f'NBY_K{num:03}';cfg=json.loads(json.dumps(base).replace('NBV_','NBY_').replace('cx-native-tx1e','cx-native-tx1f'))
 cfg.update(attempt=a,command=['python3','NBY_gate.py',a,'verifier::candidate::NBY_opening::'+name,'--cbmc-args','--unwinding-assertions'],sources=['NBY_src/Cargo.lock','NBY_gate.py','NBY_src/KMX_stubs.rs','NBY_KMX_copy_stubs.patch','NBY_src/crates/aspis-r1-cost-probe/src/lib.rs']+['NBY_src/'+n for n in files],expected_negative=neg)
 cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
