from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBJ_host as h
# Append only new native source cuts. Never mutate imported proved modules.
keys=r'''
#[kani::proof] #[kani::unwind(2)]
fn NBJ_padding_option_error(){let result:Option<usize>=kani::any();let actual=result.ok_or(Error::Merkle);match result{None=>assert!(matches!(actual,Err(Error::Merkle))),Some(c)=>assert!(matches!(actual,Ok(x) if x==c))}}
#[kani::proof] #[kani::unwind(34)]
fn NBJ_roots_projection(){let roots:[[u8;32];2]=kani::any();let folded:[u8;32]=kani::any();let t:usize=kani::any();let c:usize=kani::any();kani::assume(t<3&&c<32);let [root0,root1]=roots;let forwarded=[root0,root1,folded];assert_eq!(forwarded[t][c],if t==2{folded[c]}else{roots[t][c]});}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_slot_view_pointer(){let proof=[0u8;57607];let s:usize=kani::any();kani::assume(s<6);let q=slot(&proof,s);let begin=compact::slot_offset(s);let end=compact::slot_offset(s+1);assert_eq!(q.len(),end-begin);assert_eq!(q.len(),32*SLOT_NODES[s]);assert_eq!(q.as_ptr(),proof[begin..].as_ptr());}
'''
mp=r'''
#[kani::proof] #[kani::unwind(2)]
fn NBJ_count_copy_prefix(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&k<16);let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],if k<n{input[k]}else{0});}
#[kani::proof] #[kani::unwind(34)]
fn NBJ_level_terminal(){let idx:[u32;16]=kani::any();let val:[[u8;32];16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let at:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(n>0&&n<=16&&i==n&&w>0&&w<=i&&at<=5504&&k<16&&c<32);let mut next_n=n;let old_idx=idx[k];let old_val=val[k][c];if i>=n{next_n=w;}assert_eq!(next_n,w);assert_eq!(idx[k],old_idx);assert_eq!(val[k][c],old_val);assert_eq!(at,at);}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_count_guard(){let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();kani::assume(n<=16&&w<=i&&i<=n);if i<n{assert!(i<16&&w<16);let j=i;assert!(j<=n);}else{assert_eq!(i,n);assert!(w<=16)}}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_verify_mod32(){let length:usize=kani::any();kani::assume(length<=5504);assert_eq!(length%32==0,32*(length/32)==length);}
'''
# Applied only after the current batch is terminal.
if '--upload' not in sys.argv:raise SystemExit('use --upload after terminal receipt')
files={};name=None;lines=[]
for l in (E/'NBJ_harness.patch').read_text().splitlines(True)+['--- END\n']:
 if l.startswith('--- '):
  if name and name.endswith(('NBJ_keys.rs','NBJ_multiproof.rs')):files[name]=''.join(lines)
  name=None;lines=[]
 elif l.startswith('+++ b/'):name=l[6:].strip()
 elif name and l.startswith('+'):lines.append(l[1:])
files['crates/aspis-r1-cost-probe/src/NBJ_keys.rs']+=keys;files['crates/aspis-r1-cost-probe/src/NBJ_multiproof.rs']=files['crates/aspis-r1-cost-probe/src/NBJ_multiproof.rs'].replace('c<32 && a%2==0','c<32')+mp
for file,mod in [('candidate.rs','NBJ_keys'),('multiproof.rs','NBJ_multiproof')]:
 n='crates/aspis-r1-cost-probe/src/'+file;files[n]=(R/n).read_text()+f'\n#[cfg(kani)]\n#[path="{mod}.rs"]\nmod {mod};\n'
(E/'NBJ_harness_v4.patch').write_text((E/'NBJ_harness.patch').read_text())
patch=''
for name,new in files.items():
 old=(R/name).read_text() if (R/name).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
(E/'NBJ_harness.patch').write_text(patch)
h.admit('NBJ_LASTUPLOAD')
r=h.remote_py(f'from pathlib import Path\nb=Path({(h.B+"/NBJ_src")!r})\nfor n,s in {files!r}.items():(b/n).write_text(s)');assert r.returncode==0,r.stderr
import re
names=[('verifier::candidate::NBJ_keys::',n) for n in re.findall(r'fn (NBJ_\w+)\(\)',keys)]+[('multiproof::NBJ_multiproof::',n) for n in re.findall(r'fn (NBJ_\w+)\(\)',mp)]
for num,(mod,n) in enumerate(names,44):
 a=f'NBJ_K{num:03}';cfg=json.loads((E/'NBJ_K010.json').read_text());cfg.update(attempt=a,command=['python3','NBJ_gate.py',a,mod+n]);cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 assert not (E/a/'receipt.json').exists();(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
print('last',num)
