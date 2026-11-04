"""Full-Result native decoder/domain certificates; Unit-error runs are rejected."""
from pathlib import Path
import json,re,difflib
import NEX_validate as v
E=v.E
F={'afterdecode':'crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1','snapshotdecode':'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1'}
def undo_call(text,stub,original):
 needle=stub+'(';pos=0
 while True:
  a=text.find(needle,pos)
  if a<0:return text
  start=a+len(needle);depth=1;i=start
  while depth:
   if text[i]=='(':depth+=1
   elif text[i]==')':depth-=1
   i+=1
  args=text[start:i-1].rstrip();assert args.endswith(',f');args=args[:-2]
  replacement=original+'('+args+')';text=text[:a]+replacement+text[i:];pos=a+len(replacement)

def erasure(m,family):
 text=m['native'];name=F[family].rsplit('::',1)[1]
 text=text.replace('fn native(','pub fn '+name+'(').replace('    bytes: &[u8], f:&mut Frame,','    bytes: &[u8],')
 text=undo_call(text,'digest','decode_digest_canonical')
 text=undo_call(text,'validate','validate_verified_afterstate' if family=='afterdecode' else 'validate_pool_v1_pair_live_snapshot_v1')
 if family=='afterdecode':text=text.replace('super::super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION','super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION')
 return text

def native_attempt(a,family,mode,slot):
 m=v.read(E/(a+'-shape.json'));assert m['full_child_Result'] is True and m['mode']==mode and m['slot']==slot
 assert 'Result<Digest,crate::AtomicStatementError>' in m['source'] and 'Result<Digest,()>' not in m['source']
 assert v.sha((E/'NEX_atom_error.rs.txt').read_bytes())=='c7e81020134d5a0b8294e9f305dd4258d8686041978a8ca9af9f6aefc19f67ae'
 assert (E/'NEX_atom_error.rs.txt').read_text() in m['source']
 snap=v.native(a,mode=='positive');path=F[family].split('::')[0];f=v.inherited.frozen_source(F[family]);name=F[family].rsplit('::',1)[1];start=f.index('pub fn '+name+'(');end=f.index('\n}',start)+2
 assert m['frozen_body']==f[start:end]
 if mode in ['positive','value']:assert erasure(m,family)==m['frozen_body']
 h=f+'\n#[cfg(kani)]\n#[path="NEX_'+family+'.rs"]\nmod NEX_'+family+';\n'
 patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+path,tofile='b/'+path))+'--- /dev/null\n+++ b/'+path.rsplit('/',1)[0]+'/NEX_'+family+'.rs\n@@ -0,0 +1,'+str(len(m['source'].splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in m['source'].splitlines())
 assert snap['NEX_native_contracts.patch']==patch
 assume=re.findall(r'kani::assume\((.*?)\)',m['source'])
 assert assume==['fail_at<=21&&i<8&&k<20&&j<32']
 assert m['native'] in m['source'] and 'if n==f.fail_at{Err(NEX_atom_error())}else{Ok(f.replies[n])}' in m['source']
 base=16 if family=='afterdecode' else 128
 for text in [f'bytes[f.j]==f.bytes[{base}+32*n+f.j]','assert!(n<21)','f.digests+=1','f.digests==21&&f.validations==0','f.digests==fail_at+1&&f.validations==0','f.digests==0&&f.validations==0','f.digests==21&&f.validations==1','(Err(x),Err(e))=>assert!(x==e)']:
  assert text in m['source'],text
 fields=(['next_pair_index','next_root[i].0 as u64','next_frontier[k][i].0 as u64'] if family=='afterdecode' else ['pool[j] as u64','deployment_domain[j] as u64','sequence','next_pair_index','current_root[i].0 as u64','frontier[k][i].0 as u64'])
 expected=(['u64::from_le_bytes(f.bytes[8..16].try_into().unwrap())','f.replies[0][i].0 as u64','f.replies[1+k][i].0 as u64'] if family=='afterdecode' else ['f.bytes[48+j] as u64','f.bytes[80+j] as u64','u64::from_le_bytes(f.bytes[112..120].try_into().unwrap())','u64::from_le_bytes(f.bytes[120..128].try_into().unwrap())','f.replies[0][i].0 as u64','f.replies[1+k][i].0 as u64'])
 check='assert!(s.'+fields[slot]+'=='+expected[slot]+('^1' if mode=='value' else '')+');'
 assert m['source'].count(check)==2
 return m

def complete(family,config):
 assert family in F
 pairs=config['pairs'];count=3 if family=='afterdecode' else 6;assert len(pairs)==count
 for slot,pair in enumerate(pairs):
  assert len(pair)==2
  for a,mode in zip(pair,['positive','value']):native_attempt(a,family,mode,slot)
 for mode,slot in [('argument',0),('reply',1 if family=='afterdecode' else 4),('error',0)]:native_attempt(config['controls'][mode],family,mode,slot)
 return True
