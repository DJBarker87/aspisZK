"""Migrate selected common_contract property to explicit local snapshots.
Frozen asq8_common remains byte-for-byte untouched. Postcondition and old
expressions are retained verbatim except selected indices now come from locals.
This is direct native observation, not a new proof_for_contract certificate.
"""
from NEH_scan import *
import difflib

def paren(s,start):
 depth=1;i=start
 while depth:
  if s[i]=='(':depth+=1
  elif s[i]==')':depth-=1
  i+=1
 return s[start:i-1],i

def migrate(rp):
 directory=Path(rp).parent;patch=ROOT/directory/'NDM_harness.patch';o=dict(patched_files(patch.read_text()));adapter='programs/r1-cost-probe/src/r1_pool_adapter.rs';native='programs/r1-cost-probe/src/NDM_native.rs'
 line=next(l for l in o[adapter].splitlines() if 'kani::ensures' in l and ('asq8_common' not in l))
 pre=line.index('kani::ensures(')+len('kani::ensures(');closure,_=paren(line,pre);assert closure.startswith('|r| ');pred=closure[4:]
 def local(t):
  return t.replace('NDM_native::index8()','(record.index % 8)').replace('NDM_native::index()','record.index').replace('NDM_native::level()','record.level').replace('authenticated','a').replace('candidate_afterstate','c')
 # Protect field names: candidate_afterstate is a field too; replace identifiers only
 def local(t):
  t=t.replace('NDM_native::index8()','(record.index % 8)').replace('NDM_native::index()','record.index').replace('NDM_native::level()','record.level')
  t=re.sub(r'\bauthenticated\b','a',t)
  t=re.sub(r'(?<!\.)\bcandidate_afterstate\b','c',t)
  return t.replace('(*c)', 'c')
 pred=local(pred);olds=[]
 while 'old(' in pred:
  at=pred.index('old(');expr,end=paren(pred,at+4);olds.append(expr);pred=pred[:at]+f'old_values.{len(olds)-1}'+pred[end:]
 n=o[native];n=re.sub(r'^static mut .*\n','',n,flags=re.M);n=re.sub(r'^pub fn (?:index|index8|level)\(\).*\n','',n,flags=re.M)
 n=n.replace('#[kani::proof_for_contract(super::asq8_common)]','#[kani::proof]')
 n=n.replace('unsafe{NDM_INDEX=k;NDM_LEVEL=l;}','let record=Record{index:k,level:l};')
 assert 'NDM_INDEX' not in n and 'NDM_LEVEL' not in n
 # Input snapshots precede actual call; no equality reads a post-call input as pre-state.
 oldexpr=', '.join(olds)+','
 n=n.replace(' let _=asq8_common(&a,&c);',f' let old_values=({oldexpr});\n let r=asq8_common(&a,&c);\n assert!({pred});')
 n='struct Record{index:usize,level:usize}\n'+n
 # Only original root and native module are required. Remove unrelated snapshot hooks.
 lib='programs/r1-cost-probe/src/lib.rs';result={lib:frozen(lib).decode()+'\n#[cfg(kani)] mod NDM_kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n',adapter:frozen(adapter).decode()+'\n#[cfg(kani)] #[path="NDM_native.rs"] mod NDM_native;\n',native:n,'programs/r1-cost-probe/src/NDM_reference.rs':o['programs/r1-cost-probe/src/NDM_reference.rs']}
 result[lib]='#![cfg_attr(kani, feature(allocator_api))]\n'+result[lib]
 assert all(not re.search(r'\bstatic\s+mut\b',t) for t in result.values())
 if False: # K072 timed out in the contract layer; subsequent targets are direct selected observations
  result[native]=result[native].replace('#[kani::proof]','#[kani::proof_for_contract(super::asq8_common)]')
  result[adapter]=result[adapter].replace('fn asq8_common(',line+'\nfn asq8_common(')
 stem=Path(rp).parent.name
 out=E/(f'NEH_{stem}_local.json');out.write_text(json.dumps(result,indent=2)+'\n')
 review=dict(original_receipt=rp,patch_sha256=sha(patch.read_bytes()),method=('preserved proof_for_contract with local record' if '#[kani::proof_for_contract' in result[native] else 'direct local native observation; no replacement proof_for_contract credit'),original_predicate=closure[4:],local_predicate=pred,old_snapshots=olds,unchanged_native_body_sha256=sha(frozen(adapter)),function='r1_pool_adapter::asq8_common',harness='r1_pool_adapter::NDM_native::common_contract',discarded='unused static index helpers and unrelated harness modules; indices are local arbitrary Record fields')
 (E/(f'NEH_{stem}_migration.json')).write_text(json.dumps(review,indent=2)+'\n');return out
if __name__=='__main__':
 d=read_json(ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json')[0]
 for rp in d['kani_receipt_paths']+d['control_receipts']:migrate(rp)
