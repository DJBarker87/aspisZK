"""Split original Box/common postconditions into local-index contract windows."""
from NEK_priority import *
import re

def split_and(t):
 depth=0;start=0;out=[];i=0
 while i<len(t):
  if t[i] in '([{':depth+=1
  elif t[i] in ')]}':depth-=1
  if depth==0 and t[i:i+2]=='&&':out.append(t[start:i].strip());start=i+2;i+=1
  i+=1
 out.append(t[start:].strip());return out

def make(rp):
 patch=ROOT/Path(rp).parent/'NDM_harness.patch';o=dict(patched_files(patch.read_text()));p='programs/r1-cost-probe/src/r1_pool_adapter.rs';m='programs/r1-cost-probe/src/NDM_native.rs';old=frozen(p).decode();source=o[p]
 line=next(l for l in source.splitlines() if 'kani::ensures' in l)
 at=line.index('kani::ensures(')+len('kani::ensures(');depth=1;end=at
 while depth:
  if line[end]=='(':depth+=1
  elif line[end]==')':depth-=1
  end+=1
 closure=line[at:end-1];assert closure.startswith('|r| ');pred=closure[4:]
 pred=pred.replace('NDM_native::index8()','(record.index % 8)').replace('NDM_native::index()','record.index').replace('NDM_native::level()','record.level')
 clauses=split_and(pred)
 n=o[m];n=re.sub(r'^static mut .*\n','',n,flags=re.M);n=re.sub(r'^pub fn (?:index|index8|level)\(\).*\n','',n,flags=re.M)
 n=n.replace('unsafe{NDM_INDEX=k;NDM_LEVEL=l;}','let record=NEK_Context{index:k,level:l};').replace('asq8_common(&a,&c)','asq8_common(&a,&c,&record)').replace('crate::NDM_kmx','crate::NEK_kmx')
 n='pub(super) struct NEK_Context{pub(super) index:usize,pub(super) level:usize}\n'+n
 assert 'static mut' not in n
 sig='fn asq8_common(\n';assert old.count(sig)==1
 old=old.replace(sig,sig+'    record:&NDM_native::NEK_Context,\n')
 # Parameter first avoids editing the concrete borrowed return record type.
 old=old.replace('asq8_common(authenticated, candidate_afterstate)','asq8_common(&NDM_native::NEK_Context{index:0,level:0},authenticated,candidate_afterstate)')
 n=n.replace('asq8_common(&a,&c,&record)','asq8_common(&record,&a,&c)')
 # Bounds derive from original arbitrary harness k/l domain; no new input constraint.
 req='#[cfg_attr(kani,kani::requires(record.index<32 && record.level<aspis_statement::pool_v1::POOL_V1_PAIR_TREE_DEPTH))]\n'
 o=kmx('programs/r1-cost-probe');o[p]=old+'\n#[cfg(kani)] #[path="NDM_native.rs"] mod NDM_native;\n';o[m]=n;o['programs/r1-cost-probe/src/NDM_reference.rs']=dict(patched_files(patch.read_text()))['programs/r1-cost-probe/src/NDM_reference.rs']
 return o,p,m,req,clauses

def run(start=39):
 c=read_json(ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json')[0]
 index=start;plan=[]
 # Scalar metadata was the timed-out old combined shape; isolate each conjunct.
 for rp in c['kani_receipt_paths']:
  o,p,m,req,clauses=make(rp)
  for j,clause in enumerate(clauses):
   for neg in [False,True]:
    a=f'NEK_K{index:03}';index+=1;plan.append(dict(attempt=a,original=rp,clause=j,negative=neg,predicate=clause))
    if (E/a/'receipt.json').exists():continue
    oo=dict(o);predicate=('!('+clause+')') if neg else clause
    attr=req+'#[cfg_attr(kani,kani::ensures(|r| '+predicate+'))]\n'
    oo[p]=o[p].replace('fn asq8_common(',attr+'fn asq8_common(',1)
    v=publish(a,rp,oo,neg,'split original Box common contract conjunct; same original name, native body and typed domain; explicit local index argument; shape admission remains required')
    if 'error: could not compile' in (E/a/'stdout.log').read_text():raise SystemExit('own compile error; repair before next attempt')
    if v=='OPEN':
     (E/(a+'_OPEN.md')).write_text('No unchanged retry. Exact original conjunct remains OPEN; proceed with independent conjuncts.\n')
  (E/'NEK_COMMON_SPLIT_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 39)
