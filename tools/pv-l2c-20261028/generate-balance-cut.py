from pathlib import Path
import re,json,hashlib,sys,subprocess
R=Path(__file__).resolve().parents[2];T=R/'tools/pv-l2c-20261028/differential';E=R/'evidence/pv-l2c-20261028';parts=['use aspis_core::field::{M31,QM31};'];records=[]
def take(p,name,kind='fn'):
 s=(R/p).read_text();m=re.search(r'^(?:pub(?:\(crate\))? )?'+kind+' '+name+r'\b',s,re.M);assert m
 a=m.start();brace=s.index('{',a);b=brace+1;depth=1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 if kind=='enum':a=s.rfind('#[derive',0,a)
 body=s[a:b];parts.append(body);records.append(dict(path=p,line=s[:a].count('\n')+1,body_sha256=hashlib.sha256(body.encode()).hexdigest(),body=body))
p='crates/aspis-statement/src/state_only_poseidon.rs';s=(R/p).read_text();body=re.search(r'^pub const STATE_ONLY_POSEIDON_TRACE_ROWS:.*;',s,re.M)[0];parts.append(body);records.append(dict(path=p,body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest()))
p='crates/aspis-prover/src/state_only_hiding.rs';take(p,'StateOnlyMaskBuildError','enum')
for ty in ['m31','qm31']:
 for name in ['balance_'+ty+'_copy_inactive','sum_'+ty+'_copy_inactive','inactive_'+ty+'_step']:take(p,name)
p='crates/aspis-prover/src/prover_commit_reference.rs'
for ty in ['m31','qm31']:
 for name in ['balance_'+ty+'_owned','balance_'+ty+'_rows','balance_'+ty+'_step']:take(p,name)
body='\n\n'.join(parts)+'\n';out=T/'balance_cut.rs'
if '--check' in sys.argv:assert out.read_text()==body
else:out.write_text(body)
(E/'balance-cut-sources.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),classification='verbatim finite differential source cut, not a universal native-link proof',declarations=records),indent=2)+'\n')
print('Verified',len(records),'verbatim declarations')
