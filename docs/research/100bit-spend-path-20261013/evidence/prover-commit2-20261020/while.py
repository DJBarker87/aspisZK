from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/src/crates/aspis-r1-cost-probe/src/prover.rs')
s=p.read_text()
a='    for index in 0..aspis_core::r0::FIBRE_COUNT {\n        salts.push(reserved.derive_pool_v1_leaf_salt(hash,context,tag,index as u32).map_err(|_|Error::Semantic)?);\n    }'
b='    let mut index=0usize;\n    while index<aspis_core::r0::FIBRE_COUNT {\n        let salt=match reserved.derive_pool_v1_leaf_salt(hash,context,tag,index as u32) {\n            Ok(salt)=>salt,\n            Err(_)=>return Err(Error::Semantic),\n        };\n        salts.push(salt);\n        index+=1;\n    }'
assert s.count(a)==1
p.write_text(s.replace(a,b))
