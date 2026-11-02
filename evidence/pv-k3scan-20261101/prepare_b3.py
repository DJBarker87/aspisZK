from pathlib import Path
import subprocess,json,lzma,hashlib,base64,re
E=Path(__file__).resolve().parent;REV='daa87066400b0b8e72117f0d9f8bbefb8f2ecc2e';REF='4bc59099b98552f79d92d2a2ce289dab3faedbaa';B='tools/pv-b3p6-20261028/';sha=lambda b:hashlib.sha256(b).hexdigest()
def git(rev,p):return subprocess.check_output(['git','show',rev+':'+p],stderr=subprocess.DEVNULL)
# Immutable run input tables first, never the overwritten shared host workspace.
runs={}
for ident in ['K72122','K72135']:
 b=git(REF,'evidence/pv-b3p6-20261028/resume16/receipts/'+ident+'-inputs.json');(E/(ident+'-inputs.recovered.json')).write_bytes(b);runs[ident]=json.loads(b)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'Cargo.toml','Cargo.lock','crates/aspis-core','crates/aspis-statement','crates/aspis-prover','docs/research/v8-r0-zk-20261009/refine/poseidon',B+'v244',B+'v244-leaf16',B+'kmx'],text=True).splitlines()
files={p:git(REV,p) for p in paths};records=[]
for n,h in runs['K72135']['source_hashes'].items():
 b=(E/'blobs'/(h+'.rs')).read_bytes() if (E/'blobs'/(h+'.rs')).exists() else git(REV,n)
 assert sha(b)==h,(n,h,sha(b));files[n]=b;records.append({'path':n,'sha256':h,'immutable_run':'K72135'})
# Recover every K72122 missing source from a hash-matching historical git object.
recovered=[]
for n,h in runs['K72122']['source_hashes'].items():
 if (E/'blobs'/(h+'.rs')).exists():b=(E/'blobs'/(h+'.rs')).read_bytes();origin='retained byte-hash blob'
 else:
  b=None
  for r in [runs['K72122']['revision'],REV]+subprocess.check_output(['git','log',REF,'--format=%H','--',n],text=True).splitlines():
   try:c=git(r,n)
   except subprocess.CalledProcessError:continue
   if sha(c)==h:b=c;origin=r+':'+n;break
  assert b is not None,(n,h)
  (E/'blobs'/(h+'.rs')).write_bytes(b)
 recovered.append({'path':n,'sha256':h,'origin':origin})
# The older/newer reconstruction assertions and helper definitions must be identical.
old=(E/'blobs'/(runs['K72122']['source_hashes'][B+'v244/equivalence16.rs']+'.rs')).read_text();eq=files[B+'v244/equivalence16.rs'].decode()
def block(t,name):
 m=re.search(r'((?:#\[[^\n]*\]\s*)+)fn '+name+r'\(',t);assert m,name
 a=t.index('{',m.end());i=a;depth=1
 while depth:i+=1;depth+=(t[i]=='{')-(t[i]=='}')
 return t[m.start():i+1]
assert block(old,'reconstruct_10')==block(eq,'reconstruct_10')
# Selected-module projection: retain original helpers + original reconstruct body;
# unrelated proof functions containing global-oracle stub attributes are excluded.
prefix=eq[:eq.index('#[kani::proof]')];selected=prefix+block(eq,'reconstruct_10')+'\n'
selected=selected.replace('assert_eq!(dep::reconstruct(&v),reference::reconstruct(&v));','if cfg!(feature="negative-reconstruct") { assert_ne!(dep::reconstruct(&v),reference::reconstruct(&v)); } else { assert_eq!(dep::reconstruct(&v),reference::reconstruct(&v)); }')
files[B+'v244/equivalence16.rs']=selected.encode()
t=files[B+'v244/lib_leaf16.rs'].decode();assert t.count('#[cfg(kani)] mod shared_callee16;')==1;t=t.replace('#[cfg(kani)] mod shared_callee16;','// Unselected shared memo oracle omitted; selected harnesses never call it.');files[B+'v244/lib_leaf16.rs']=t.encode()
t=files[B+'v244/remaining_equivalence16.rs'].decode();oldassert='assert_eq!(d::validate(p),r::validate(p));';assert t.count(oldassert)==1;t=t.replace(oldassert,'if cfg!(feature="negative-transition") { assert_ne!(d::validate(p),r::validate(p)); } else { '+oldassert+' }');files[B+'v244/remaining_equivalence16.rs']=t.encode()
manifest=B+'v244-leaf16/Cargo.toml';assert sha(files[manifest])==runs['K72135']['manifest_sha256'];t=files[manifest].decode();t=t.replace('[features]','[features]\nnegative-reconstruct=[]\nnegative-transition=[]');files[manifest]=t.encode()
assert sha(files[B+'kmx/KMX_stubs.rs'])==runs['K72135']['KMX_stubs_sha256']
# Remove unrelated root workspace members, keeping every reached body unchanged.
t=files['Cargo.toml'].decode();t=re.sub(r'members\s*=\s*\[.*?\]', 'members=["crates/aspis-core","crates/aspis-statement","crates/aspis-prover","docs/research/v8-r0-zk-20261009/refine/poseidon"]',t,count=1,flags=re.S);files['Cargo.toml']=t.encode()
# Store all original module bytes, including excluded ones, for auditability.
raw=json.dumps({n:base64.b64encode(b).decode() for n,b in files.items()}).encode();(E/'B3-source.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'B3-source.json.sha256').write_text(sha(raw)+'\n')
(E/'B3-SOURCE-CLOSURE.json').write_text(json.dumps({'base_revision':REV,'selected_current_credits':['C155','C157'],'source_records':records,'recovered_K72122':recovered,'selection_changes':['Original complete source modules and constants retained','Original reconstruct_10 same body in both immutable snapshots; helpers unchanged','Unselected global shared_callee16 module and its unrelated proof functions omitted from selected crate root; no native function/stub/body/domain changed','Feature-only inversions of the two original selected assertions','Workspace membership reduced to present dependencies; selected manifest package/features/dependencies retained'],'excluded_global_credits':['C156 equivalence16::shared_repeat16','C163 equivalence17::sum_high_nodes K73931','C164 equivalence17::sum_high_path K73932'],'warning':'Their global memo properties remain SUSPENDED. The projection is for reconstruct/transition only and supplies no replacement shared-callee or full op227 law.'},indent=2)+'\n')
print(len(files),'pinned/projected files',len(raw),'payload bytes')
