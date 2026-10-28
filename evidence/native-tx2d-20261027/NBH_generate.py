from pathlib import Path
import subprocess,re,difflib,json,hashlib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'; ROOT='crates/aspis-statement/src/pool_v1/'
def frozen(f):return subprocess.check_output(['git','show',REV+':'+ROOT+f],text=True)
def body(f,name):
 s=frozen(f); start=s.index('{',s.index('fn '+name+'(')); depth=1;i=start+1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 return s[start+1:i-1]
# Digest contract is discharged by NBD_DigestInduction.source, all raw limbs.
contract='''use super::*;
fn NBH_digest(d: &Digest) -> bool {
 let b: bool = kani::any();
 kani::assume(b == (d[0].0 < P && d[1].0 < P && d[2].0 < P && d[3].0 < P && d[4].0 < P && d[5].0 < P && d[6].0 < P && d[7].0 < P)); b
}
'''
files={}; probes={}
for f,name,owner,error in [('pair_terminal.rs','validate_verified_afterstate','afterstate','PoolV1PairVerifierTransportErrorV1'),('pair_tree_profile.rs','validate_pool_v1_pair_live_snapshot_v1','snapshot','PoolV1PairLiveSnapshotErrorV1')]:
 b=body(f,name); loop=b[b.index('    while level'):b.index('    Ok(())')]
 assert loop.count('while')==1
 one=loop.replace('while level','if level').replace('return Err(', 'return (level, Some(').replace(');', '));') if False else loop.replace('while level','if level').replace('return Err('+error+'::','return (level, Some('+error+'::').replace('Digest);','Digest));').replace('Afterstate);','Afterstate));')
 # Abstract frontier only; native loop reads no other record fields.
 one=one.replace(owner+'.'+('next_frontier' if owner=='afterstate' else 'frontier'),'frontier')
 cname='crate::pool_v1::pair_tree_profile::digest_is_canonical'
 one=one.replace('super::pair_tree_profile::digest_is_canonical','NBH_digest').replace('digest_is_canonical','NBH_digest')
 # Callee replacement is explicit in transformation receipt; paired theorem below.
 suffix='after' if owner=='afterstate' else 'live'
 frontier='['+','.join('['+','.join('M31(kani::any())' for _ in range(8))+']' for _ in range(20))+']'
 result='NonCanonicalAfterstate' if suffix=='after' else 'NonCanonicalDigest'
 code=contract+f'''fn NBH_{suffix}_iteration(frontier: &[Digest;20], mut level: usize) -> (usize, Option<{error}>) {{
{one}
(level,None)
}}
#[kani::proof]
fn NBH_{suffix}_step() {{
 let frontier: [Digest;20] = {frontier};
 let level: usize = kani::any(); kani::assume(level<=20);
 let got=NBH_{suffix}_iteration(&frontier,level);
 let expected=if level==20 {{(level,None)}} else if NBH_digest(&frontier[level]) {{(level+1,None)}} else {{(level,Some({error}::{result}))}};
 assert_eq!(got,expected);
}}
'''
 child='NBH_'+suffix
 files[ROOT+child+'.rs']=code
 probes[suffix]={'source_loop':loop,'sha256':hashlib.sha256(loop.encode()).hexdigest(),'one_iteration':one,'transformation':'while to if; return error exposes level; digest call replaced by Lean-discharged all-raw-limb contract; invariant level<=20'}
 # Exact prefix: retains all checks up to the frontier loop, exposes pending suffix.
 prefix=b[:b.index('    let mut level')]
 prefix=prefix.replace('super::pair_tree_profile::digest_is_canonical','NBH_digest').replace('!digest_is_canonical','!NBH_digest')
 # Function retains all field reads, complete arbitrary typed records generated below.
 decl=frozen(f).split('fn '+name+'(',1)[1].split(') ->',1)[0]
 # prefix return type maps success to None (pending suffix) and error to Some.
 prefix=prefix.replace('return Err(', 'return Some(').replace('super::POOL_V1_PAIR_CAPACITY','crate::pool_v1::POOL_V1_PAIR_CAPACITY')
 # generate record constructor by extracting fields with recursion
 def ctor(ty):
  if ty in ['u8','u32','u64','[u8; 32]']:return 'kani::any()'
  if ty=='Digest':return '['+','.join('M31(kani::any())' for _ in range(8))+']'
  if ty.startswith('[Digest;'):return '['+','.join(ctor('Digest') for _ in range(20))+']'
  bs=frozen(f).split('pub struct '+ty+' {',1)[1].split('\n}',1)[0]
  return ty+'{'+','.join(n+':'+ctor(t) for n,t in re.findall(r'^    pub (\w+): ([^\n]+),$',bs,re.M))+'}'
 ty=decl.split(': &')[1].strip().strip(','); record=ctor(ty)
 expected=(f'''if {owner}.next_pair_index==0 || {owner}.next_pair_index>1048576 {{Some({error}::InvalidAfterstateIndex)}} else if !NBH_digest(&{owner}.next_root) {{Some({error}::NonCanonicalAfterstate)}} else {{None}}''' if suffix=='after' else f'''if {owner}.pool==[0;32] || {owner}.deployment_domain==[0;32] {{Some({error}::ZeroRequiredBinding)}} else if {owner}.sequence!={owner}.next_pair_index {{Some({error}::SequenceIndexMismatch)}} else if {owner}.next_pair_index>=1048576 {{Some({error}::TreeFull)}} else if !NBH_digest(&{owner}.current_root) {{Some({error}::NonCanonicalDigest)}} else {{None}}''')
 files[ROOT+child+'.rs']+=f'''fn NBH_{suffix}_prefix({decl}) -> Option<{error}> {{{prefix} None}}
#[kani::proof]
fn NBH_{suffix}_prefix_gate() {{ let {owner}={record}; assert_eq!(NBH_{suffix}_prefix(&{owner}),{expected}); }}
'''
 probes[suffix]['prefix']=prefix
# Actual exact helper: arbitrary bounded slices; fixed width 8 and32.
f='pair_terminal.rs';child='NBH_after';
for n in [8,32]:
 files[ROOT+child+'.rs']+=f'''#[kani::proof]
fn NBH_exact{n}() {{ let bytes: [u8;64]=kani::any(); let len: usize=kani::any(); kani::assume(len<=64);
 let got=exact::<{n}>(&bytes[..len]);
 if len=={n} {{ let out=got.unwrap(); let j:usize=kani::any(); kani::assume(j<{n}); assert_eq!(out[j],bytes[j]); }} else {{assert_eq!(got,Err(PoolV1PairVerifierTransportErrorV1::WrongLength));}}
}}
'''
exec((E/'NBH_extra.py').read_text())
exec((E/'NBH_extra2.py').read_text())
files={p:s.replace('super::POOL_','crate::pool_v1::POOL_') for p,s in files.items()}
patch=''
for f,child in [('pair_terminal.rs','NBH_after'),('pair_tree_profile.rs','NBH_live'),('verifier_registry.rs','NBH_registry'),('format.rs','NBH_format'),('pair_forest_terminal.rs','NBH_terminal'),('pair_forest_accounts.rs','NBH_accounts')]:
 old=frozen(f);new=old+'\n#[cfg(kani)]\n#[path="'+child+'.rs"]\nmod '+child+';\n'
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+ROOT+f,tofile='b/'+ROOT+f))
for p,s in files.items():patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+p))
(E/'NBH_harness.patch').write_text(patch)
(E/'NBH_NATIVE_PROBES.json').write_text(json.dumps(probes,indent=2)+'\n')
