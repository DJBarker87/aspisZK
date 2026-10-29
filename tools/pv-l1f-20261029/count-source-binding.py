"""Record exact deployed count-field reads, without claiming whole-plan refinement."""
from pathlib import Path
import hashlib,json,subprocess,re
E=Path('evidence/pv-l1f-20261029');p=Path('tools/r1-cost-probe/src/bin/devnet_spend/plan.rs')
s=p.read_text();rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.check_output(['git','show',rev+':'+str(p)])==p.read_bytes()
start=s.index(' let result=RealR1_client::prove_for_proof_accounts(')
end=s.index('\n}',start);suffix=s[start:end]
expected=['accounts.selected(result.attempts)?','accounts.publication(result.attempts,','"attempts":result.attempts']
assert suffix.count('result.attempts')==3
assert all(suffix.count(x)==1 for x in expected)
assert not re.search(r'\b(?:mut\s+result|result\s*=|result\.attempts\s*=)',suffix)
checks=[]
for text in expected:
 at=s.index(text,start);checks.append(dict(statement=text,line=s.count('\n',0,at)+1,sha256=hashlib.sha256(text.encode()).hexdigest()))
(E/'count-source-reads.json').write_text(json.dumps(dict(source_revision=rev,path=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),suffix_sha256=hashlib.sha256(suffix.encode()).hexdigest(),reads=checks,scope='Selected direct immutable field reads only; not complete plan/world binding or delivery.',native_field='RetriedProof.attempts; emitted read is attempts.val',deployed_configuration=dict(toolchain='1.94.1',profile='release',features=['r1p-check','aspis-r1-cost-probe/ct-host-prover']),compiler_boundary='V370 at pending D381/D386',open=['earlier source count/rejection acquisition','full ordered native/world prefix','joint D163-to-simE occurrence and failure coupling']),indent=2)+'\n')
