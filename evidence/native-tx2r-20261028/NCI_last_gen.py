from NCI_extend import edit,attrs
import subprocess,hashlib,json
from pathlib import Path
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
cut='''        let q=queries[i];
        if q>=1<<18||queries[..i].contains(&q){return Err(Error::Checkpoint);}
        i+=1;
'''
assert s.count(cut)==1
h='\n#[cfg(kani)] mod NCI_query_step {\nuse super::*;\nfn iteration(queries:&[u32;22],mut i:usize)->Result<usize,Error>{\n'+cut+'Ok(i)}\n'
for wrong in [False,True]:
 h+=attrs+f'''fn duplicate_{'wrong' if wrong else 'ok'}(){{let mut q:[u32;22]=kani::any();kani::assume(q[0]<1<<18);q[1]=q[0];let out=iteration(&q,1);assert!(out.is_err(){'!=' if wrong else '=='}true);}}\n'''
h+='}\n'
edit('NCI_last.patch',lambda s:s.replace('let _=strong(&mut r,0);','let _=weak(&mut r,0);')+h)
(E/'NCI_QUERY_STEP_SOURCE.json').write_text(json.dumps({'source':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','cut':cut,'sha256':hashlib.sha256(cut.encode()).hexdigest(),'scope':'one lexical outer step, prefix length1; not complete validator'},indent=2)+'\n')
jobs=[('verifier::NCI_query_step::duplicate_ok',False),('verifier::NCI_query_step::duplicate_wrong',True),('verifier::NCI_contracts::parent_domain',True)]
(E/'NCI_last_queue.json').write_text(json.dumps([dict(attempt=f'NCI_K{i:03}',harness=h,patch='NCI_last.patch',negative=negative) for i,(h,negative) in enumerate(jobs,68)],indent=2)+'\n')
