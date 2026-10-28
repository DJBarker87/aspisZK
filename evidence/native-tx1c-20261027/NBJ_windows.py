from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBJ_host as h
# Recover the final patch source additions without evaluating an older generator.
files={};name=None;lines=[]
for l in (E/'NBJ_harness.patch').read_text().splitlines(True)+['--- END\n']:
 if l.startswith('--- '):
  if name and name.endswith(('NBJ_keys.rs','NBJ_multiproof.rs')):files[name]=''.join(lines)
  name=None;lines=[]
 elif l.startswith('+++ b/'):name=l[6:].strip()
 elif name and l.startswith('+'):lines.append(l[1:])
keysname='crates/aspis-r1-cost-probe/src/NBJ_keys.rs';keys=files[keysname]
# Do not launch any other fixed-opening832-byte shape after K010.
for w in range(26):
 keys+=f'''
#[kani::proof] #[kani::unwind(2)]
fn NBJ_opening_word_{w:02}(){{
 let c:usize=kani::any();let b:u8=kani::any();kani::assume(c<32);
 let mut proof=[0u8;57607];proof[{10055+32*w}+c]=b;
 let q=opening(&proof,0);let selected=&q[{32*w}..{32*(w+1)}];
 assert_eq!(selected.len(),32);assert_eq!(selected[c],b);assert_eq!(selected.as_ptr(),proof[{10055+32*w}..].as_ptr());
}}
'''
files[keysname]=keys
for file,mod in [('candidate.rs','NBJ_keys'),('multiproof.rs','NBJ_multiproof')]:
 n='crates/aspis-r1-cost-probe/src/'+file;files[n]=(R/n).read_text()+f'\n#[cfg(kani)]\n#[path="{mod}.rs"]\nmod {mod};\n'
(E/'NBJ_harness_v3.patch').write_text((E/'NBJ_harness.patch').read_text())
patch=''
for name,new in files.items():
 old=(R/name).read_text() if (R/name).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
(E/'NBJ_harness.patch').write_text(patch)
h.admit('NBJ_WORDUPLOAD')
r=h.remote_py(f'from pathlib import Path\nb=Path({(h.B+"/NBJ_src")!r})\nfor n,s in {files!r}.items():(b/n).write_text(s)');assert r.returncode==0,r.stderr
for w,num in enumerate(list(range(11,32))+list(range(39,44))):
 a=f'NBJ_K{num:03}';cfg=json.loads((E/'NBJ_K010.json').read_text());cfg.update(attempt=a,command=['python3','NBJ_gate.py',a,f'verifier::candidate::NBJ_keys::NBJ_opening_word_{w:02}']);cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 assert not (E/a/'receipt.json').exists();(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
