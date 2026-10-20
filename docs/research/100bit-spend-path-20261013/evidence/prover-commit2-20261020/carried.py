from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/src/crates/aspis-r1-cost-probe/src/prover.rs')
s=p.read_text()
a='    let mut index=0usize;\n    while index<aspis_core::r0::FIBRE_COUNT {\n        salts=derive_private_salt_step(reserved,context,hash,tag,index as u32,salts)?;\n        index+=1;\n    }\n    Ok(PrivateSalts::new(salts))'
b='    let mut result=Ok(salts);\n    let mut index=0usize;\n    while index<aspis_core::r0::FIBRE_COUNT {\n        result=match result {\n            Ok(salts)=>derive_private_salt_step(reserved,context,hash,tag,index as u32,salts),\n            Err(error)=>Err(error),\n        };\n        index+=1;\n    }\n    result.map(PrivateSalts::new)'
assert s.count(a)==1
p.write_text(s.replace(a,b))
