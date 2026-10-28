from pathlib import Path
import sys,json,re,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBV_host as h
attrs='''#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
def extract(patch,ends):
 name=None;lines=[]
 for l in patch.read_text().splitlines(True)+['--- END\n']:
  if l.startswith('--- '):
   if name and name.endswith(ends):return ''.join(lines)
   name=None;lines=[]
  elif l.startswith('+++ b/'):name=l[6:].strip()
  elif name and l.startswith('+'):lines.append(l[1:])
 raise ValueError(ends)
# Recheck inherited copy-exposed helpers under the exact KMX replacements.
old=extract(R/'evidence/native-tx1a-20261027/NBE_harness.patch','NBE_keys.rs')
old=old.replace('NBE_','NBV_R_')
old=old.replace('#[kani::proof]',attrs+'#[kani::proof]')
# Most original unwinds were low because memcpy did not unwind. Need copied salt32 / prefix sizes.
old=re.sub(r'#\[kani::unwind\(\d+\)\]','#[kani::unwind(34)]',old)
# Original leaf body checks native byte addresses; no whole leaf copy introduced.
(E/'NBV_replay_keys.rs.txt').write_text(old)
mp=(E/'NBV_multiproof.rs.txt').read_text()
mp+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+'''fn NBV_parent_reply_wrong(){let val=[[0u8;32];16];let answer=[1u8;32];let calls=Cell::new(0);let hash=Port{left:val[0].as_ptr(),right:val[1].as_ptr(),c:31,l:0,r:0,answer,calls:&calls};let out=occupied_binary_parent(hash,&val,0);assert_eq!(out[31],0);}
#[kani::proof] #[kani::unwind(34)]
'''+attrs+'''fn NBV_admitted_copy_wrong(){let mut input=[0u32;16];for i in 0..16{input[i]=i as u32;}assert!(well_formed(&input));let mut level=[0u32;16];level[..16].copy_from_slice(&input);assert_eq!(level[15],0);}
'''
# Source selected-store frame independent old copied carrier, count equal-parent step.
mp+='''#[kani::proof] #[kani::unwind(2)]
fn NBV_count_native_step(){let mut level:[u32;16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();let count:usize=kani::any();kani::assume(i<=j&&j<=n&&i<n&&n<=16&&w<=i&&k<16&&count<=288);let parent=index_at(&level,i)>>Arity::Two.bits();let old=level[k];let mut next_j=j;if next_j<n&&index_at(&level,next_j)>>Arity::Two.bits()==parent{next_j+=1;}assert_eq!(next_j,j+usize::from(j<n&&level[j]/2==parent));assert!(next_j<=n);if j>i&&j-i<=2{let next_count=count+Arity::Two.width()-(j-i);level[w]=parent;assert_eq!(level[k],if k==w{parent}else{old});assert_eq!(next_count,count+2-(j-i));}}
#[kani::proof] #[kani::unwind(2)]
fn NBV_level_continuation(){let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();kani::assume(0<n&&n<=16&&w<=i&&i<=n);if i==n{let next_n=w;let next_i=0usize;let next_w=0usize;assert!(next_n<=16&&next_w<=next_i&&next_i<=next_n);}else{assert!(i<16&&w<16)}}
#[kani::proof] #[kani::unwind(34)]
'''+attrs+'''fn NBV_final_carrier(){let values:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let idx:[u32;16]=kani::any();let n:usize=kani::any();let at:usize=kani::any();let len:usize=kani::any();let actual=n==1&&index_at(&idx,0)==0&&root_matches(&values,&root)&&at==len;assert_eq!(actual,n==1&&idx[0]==0&&values[0]==root&&at==len);}
'''
keys=(E/'NBV_keys.rs.txt').read_text()
# One word at arbitrary native offset; source reads SAME bytes. No whole-buffer scan.
keys+='''#[kani::proof] #[kani::unwind(10)]
'''+attrs+'''fn NBV_padding_word_native(){let nodes:[u8;5504]=kani::any();let count:usize=kani::any();let cap:usize=kani::any();let k:usize=kani::any();kani::assume(count<=cap&&cap<=172&&k<4*(cap-count));let at=32*count+8*k;let q=&nodes[at..at+8];let word=u64::from_le_bytes(q.try_into().unwrap());assert_eq!(word==0,(0..8).all(|j|nodes[at+j]==0));}
'''
# Physically borrowed immutable opening: arbitrary surroundings; selected fixed byte per 32 window.
keys+='''#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_byte_window(){let proof:[u8;57607]=kani::any();let w:usize=kani::any();kani::assume(w<26);let q=opening(&proof,0);let selected=&q[32*w..32*w+32];assert_eq!(selected[0],proof[10055+32*w]);}
'''
# Negative controls for inherited leaf, write and sort use exact originals with only final false condition.
# Calls same native helper/cut; no distinct copy model.
neg=old
names=['NBV_R_leaf','NBV_R_key','NBV_R_sort']
for name in names:
 start=old.index('fn '+name+'(');brace=old.index('{',start);d=1;end=brace+1
 while d:
  if old[end]=='{':d+=1
  elif old[end]=='}':d-=1
  end+=1
 body=old[start:end].replace('fn '+name+'(','fn '+name+'_wrong(',1)
 if name=='NBV_R_leaf':body=body.replace('assert_eq!(out[c%32],answer[c%32])','assert_ne!(out[c%32],answer[c%32])')
 elif name=='NBV_R_key':body=body.replace('assert_eq!(keys[k],if k==j{expected}else{old[k]})','assert_ne!(keys[k],if k==j{expected}else{old[k]})')
 else:body=body.replace('assert_eq!(out[k],','assert_ne!(out[k],')
 old+='\n#[kani::proof] #[kani::unwind(34)]\n'+attrs+body+'\n'
files={'crates/aspis-r1-cost-probe/src/NBV_multiproof.rs':mp,'crates/aspis-r1-cost-probe/src/NBV_keys.rs':keys,'crates/aspis-r1-cost-probe/src/NBV_replay_keys.rs':old}
for f,mods in [('multiproof.rs',['NBV_multiproof']),('candidate.rs',['NBV_keys','NBV_replay_keys'])]:
 n='crates/aspis-r1-cost-probe/src/'+f;files[n]=(R/n).read_text()+''.join(f'\n#[cfg(kani)]\n#[path="{m}.rs"]\nmod {m};\n' for m in mods)
(E/'NBV_multiproof.rs.txt').write_text(mp);(E/'NBV_keys.rs.txt').write_text(keys);(E/'NBV_replay_keys.rs.txt').write_text(old)
patch=''
for n,new in files.items():
 old_s=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(old_s.splitlines(True),new.splitlines(True),fromfile='a/'+n if old_s else '/dev/null',tofile='b/'+n))
(E/'NBV_harness_stage2.patch').write_text(patch)
h.admit('NBV_UPLOAD3');r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBV_src"/n).write_text(s)');assert r.returncode==0,r.stderr
names=[('multiproof::NBV_multiproof::',n) for n in ['NBV_parent_reply_wrong','NBV_admitted_copy_wrong']]+[('verifier::candidate::NBV_replay_keys::',n) for n in ['NBV_R_leaf','NBV_R_leaf_wrong','NBV_R_key','NBV_R_key_wrong','NBV_R_sort','NBV_R_sort_wrong','NBV_R_offset']]+[('multiproof::NBV_multiproof::',n) for n in ['NBV_count_native_step','NBV_level_continuation','NBV_final_carrier']]+[('verifier::candidate::NBV_keys::',n) for n in ['NBV_padding_word_native','NBV_opening_byte_window']]
for num,(m,n) in enumerate(names,14):
 a=f'NBV_K{num:03}';cfg=json.loads((E/'NBV_K003.json').read_text());cfg.update(attempt=a,sources=['NBV_src/Cargo.lock','NBV_gate.py','NBV_src/KMX_stubs.rs','NBV_KMX_copy_stubs.patch','NBV_src/crates/aspis-r1-cost-probe/src/lib.rs']+['NBV_src/'+n for n in files],command=['python3','NBV_gate.py',a,m+n,'--cbmc-args','--unwinding-assertions']);cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
