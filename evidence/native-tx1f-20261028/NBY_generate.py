from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBY_host as h
attrs='''#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
cases=[];text='use super::*;\n'
def pair(name,body,expr):
 global text
 for neg in [False,True]:
  nn='NBY_'+name+('_wrong' if neg else '')
  text+=attrs+'fn '+nn+'(){'+body+('assert!(!('+expr+'));' if neg else 'assert!('+expr+');')+'}\n'
  cases.append((nn,neg))
def publish(mod,owner,start):
 files={'crates/aspis-r1-cost-probe/src/'+mod+'.rs':text}
 r=h.remote_py(f'from pathlib import Path\nprint(Path({(h.B+"/NBY_src/crates/aspis-r1-cost-probe/src/"+owner)!r}).read_text(),end="")');assert r.returncode==0,r.stderr
 files['crates/aspis-r1-cost-probe/src/'+owner]=r.stdout+(f'\n#[cfg(kani)]\n#[path="{mod}.rs"]\nmod {mod};\n' if f'mod {mod};' not in r.stdout else '')
 h.admit(mod+'UPLOAD')
 r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBY_src"/n).write_text(s)');assert r.returncode==0,r.stderr
 patch=''
 for n,s in files.items():
  old=(R/n).read_text() if (R/n).exists() else ''
  patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
 (E/(mod+'.patch')).write_text(patch)
 base=json.loads((E/'NBY_K001.json').read_text());scope='multiproof' if owner=='multiproof.rs' else 'verifier::candidate'
 for num,(name,neg) in enumerate(cases,start):
  a=f'NBY_K{num:03}';
  if (E/a/'receipt.json').exists():continue
  cfg=json.loads(json.dumps(base));cfg.update(attempt=a,command=['python3','NBY_gate.py',a,scope+'::'+mod+'::'+name,'--cbmc-args','--unwinding-assertions'],sources=base['sources']+['NBY_src/'+n for n in files],expected_negative=neg)
  cfg['sources']=list(dict.fromkeys(cfg['sources']));cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
  for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
  (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 print('prepared',start,start+len(cases)-1)
