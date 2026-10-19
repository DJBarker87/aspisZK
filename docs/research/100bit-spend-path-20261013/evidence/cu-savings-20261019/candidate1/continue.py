from pathlib import Path
import json
w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019')
p=w/'injections/crates/aspis-r1-cost-probe/src/verifier.rs';s=p.read_text().replace('let p=Prepared::decision1h_old_new(&sem,&v,hash)?;','if decision1h_migration_tests::before_prepare(){return Err(Error::Transcript)}\n    let p=Prepared::decision1h_old_new(&sem,&v,hash)?;');p.write_text(s)
p=w/'injections-default.json';d=json.loads(p.read_text());d['out']=str(w/'runs/c1-injections-default-harness-fix');p.write_text(json.dumps(d,indent=2))
