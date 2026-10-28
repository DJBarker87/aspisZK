from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
attrs='''#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
mp='use super::*;\n'
mp+='''#[kani::proof] #[kani::unwind(34)]
'''+attrs+'''fn NBV_count_copy_prefix(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&k<16);let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],if k<n{input[k]}else{0});}
#[kani::proof] #[kani::unwind(34)]
'''+attrs+'''fn NBV_count_copy_wrong(){let mut input=[0u32;16];input[7]=1;input[15]=512;let n=16;let k=15;let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],0);}
'''
files={'crates/aspis-r1-cost-probe/src/NBV_multiproof.rs':mp}
for file,mod in [('multiproof.rs','NBV_multiproof')]:
 n='crates/aspis-r1-cost-probe/src/'+file
 files[n]=(R/n).read_text()+f'\n#[cfg(kani)]\n#[path="{mod}.rs"]\nmod {mod};\n'
patch=''
for n,new in files.items():
 old=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NBV_harness.patch').write_text(patch)
(E/'NBV_multiproof.rs.txt').write_text(mp)
h.admit('NBV_UPLOAD1')
r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBV_src"/n).write_text(s)\n(b/"NBV_gate.py").write_text({(E/"NBV_gate.py").read_text()!r})');assert r.returncode==0,r.stderr
for num,name in enumerate(['NBV_count_copy_prefix','NBV_count_copy_wrong'],1):
 a=f'NBV_K{num:03}'
 cfg=json.loads((R/'evidence/native-tx1c-20261027/NBJ_K048.json').read_text())
 cfg.update(attempt=a,command=['python3','NBV_gate.py',a,'multiproof::NBV_multiproof::'+name,'--cbmc-args','--unwinding-assertions'],sources=['NBV_src/Cargo.lock','NBV_gate.py','NBV_src/KMX_stubs.rs','NBV_KMX_copy_stubs.patch','NBV_src/crates/aspis-r1-cost-probe/src/lib.rs']+['NBV_src/'+n for n in files])
 cfg['env']['TMPDIR']=h.B+'/NBV_tmp';cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
