from pathlib import Path
import sys,json,re,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
attrs='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
# Re-establish all three inherited row windows; no full-buffer loop.
s='';name=None;lines=[]
for l in (R/'evidence/native-tx1c-20261027/NBJ_harness.patch').read_text().splitlines(True)+['--- END\n']:
 if l.startswith('--- '):
  if name and name.endswith('NBJ_multiproof.rs'):s=''.join(lines);break
  name=None;lines=[]
 elif l.startswith('+++ b/'):name=l[6:].strip()
 elif name and l.startswith('+'):lines.append(l[1:])
assert s
s=s.replace('NBJ_','NBV_W_').replace('#[kani::proof]',attrs+'#[kani::proof]')
s=re.sub(r'#\[kani::unwind\(\d+\)\]','#[kani::unwind(34)]',s)
# Negate a property of the selected native result, never unconditional false.
for kind in ['pair','supply','short']:
 n='NBV_W_'+kind+'_window';start=s.index('fn '+n+'(');brace=s.index('{',start);d=1;end=brace+1
 while d:
  if s[end]=='{':d+=1
  elif s[end]=='}':d-=1
  end+=1
 body=s[start:end].replace('fn '+n+'(','fn '+n+'_wrong(',1)
 # Every branch checks the exact returned scalar tuple including success/rejection.
 assert 'assert_eq!(out,' in body
 body=body.replace('assert_eq!(val[0][c],','assert_ne!(val[0][c],',1)
 s+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+body+'\n'
(E/'NBV_row_windows.rs.txt').write_text(s)
k='use super::*;\n'
for neg in [False,True]:
 k+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'fn NBV_roots'+('_wrong' if neg else '')+'(){let roots:[[u8;32];2]=kani::any();let folded:[u8;32]=kani::any();let t:usize=kani::any();let c:usize=kani::any();kani::assume(t<3&&c<32);let [root0,root1]=roots;let forwarded=[root0,root1,folded];'+('assert_ne!' if neg else 'assert_eq!')+'(forwarded[t][c],if t==2{folded[c]}else{roots[t][c]});}\n'
for neg in [False,True]:
 k+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'fn NBV_opening_installed_window'+('_wrong' if neg else '')+'(){let mut proof=[0u8;57607];let i:usize=kani::any();let w:usize=kani::any();let c:usize=kani::any();let bytes:[u8;32]=kani::any();kani::assume(i<22&&w<26&&c<32);let at=10055+832*i+32*w;proof[at..at+32].copy_from_slice(&bytes);let q=opening(&proof,i);'+('assert_ne!' if neg else 'assert_eq!')+'(q[32*w+c],bytes[c]);}\n'
k+='''#[kani::proof] #[kani::unwind(2)]
fn NBV_parent_prefix_guard(){let count:usize=kani::any();let s:usize=kani::any();let d:usize=kani::any();kani::assume(s<6&&d>0&&d<=12);let observed=Some(count).ok_or(Error::Merkle);assert!(matches!(observed,Ok(x) if x==count));if count>SLOT_NODES[s]{assert!(count>SLOT_NODES[s]);}else{let width=32*count;assert!(width<=32*SLOT_NODES[s]&&width<=5504);let n=d;assert!(n>0&&n<=16);}}
'''
k+='\n#[kani::proof] #[kani::unwind(10)]\n'+attrs+'''fn NBV_padding_word_wrong(){let nodes:[u8;5504]=kani::any();let count:usize=kani::any();let cap:usize=kani::any();let j:usize=kani::any();kani::assume(count<=cap&&cap<=172&&j<4*(cap-count));let at=32*count+8*j;let q=&nodes[at..at+8];let word=u64::from_le_bytes(q.try_into().unwrap());assert_ne!(word==0,(0..8).all(|c|nodes[at+c]==0));}\n'''
(E/'NBV_parent.rs.txt').write_text(k)
if '--upload' not in sys.argv:raise SystemExit(0)
h.admit('NBV_UPLOAD5')
files={'crates/aspis-r1-cost-probe/src/NBV_row_windows.rs':s,'crates/aspis-r1-cost-probe/src/NBV_parent.rs':k}
for f,mods in [('multiproof.rs',['NBV_multiproof','NBV_row_windows']),('candidate.rs',['NBV_keys','NBV_replay_keys','NBV_leaf_rows','NBV_parent'])]:
 n='crates/aspis-r1-cost-probe/src/'+f;files[n]=(R/n).read_text()+''.join(f'\n#[cfg(kani)]\n#[path="{m}.rs"]\nmod {m};\n' for m in mods)
r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBV_src"/n).write_text(s)');assert r.returncode==0,r.stderr
patch=''
for n,new in files.items():
 o=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(o.splitlines(True),new.splitlines(True),fromfile='a/'+n if o else '/dev/null',tofile='b/'+n))
(E/'NBV_final_gates.patch').write_text(patch)
names=[('verifier::candidate::NBV_parent::',n) for n in ['NBV_roots','NBV_roots_wrong','NBV_opening_installed_window','NBV_opening_installed_window_wrong']]+[('multiproof::NBV_row_windows::','NBV_W_'+kind+'_window'+suffix) for kind in ['pair','supply','short'] for suffix in ['', '_wrong']]+[('verifier::candidate::NBV_parent::','NBV_padding_word_wrong')]
for num,(m,n) in enumerate(names,40):
 a=f'NBV_K{num:03}';cfg=json.loads((E/'NBV_K028.json').read_text());cfg.update(attempt=a,command=['python3','NBV_gate.py',a,m+n,'--cbmc-args','--unwinding-assertions']);cfg['sources']+=['NBV_src/crates/aspis-r1-cost-probe/src/'+x for x in ['NBV_row_windows.rs','NBV_parent.rs']];cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for key in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(key,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
