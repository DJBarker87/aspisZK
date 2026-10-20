from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/src/crates/aspis-r1-cost-probe/src/prover.rs')
s=p.read_text()
a='    let mut index=0usize;\n    while index<aspis_core::r0::FIBRE_COUNT {\n        let salt=match reserved.derive_pool_v1_leaf_salt(hash,context,tag,index as u32) {\n            Ok(salt)=>salt,\n            Err(_)=>return Err(Error::Semantic),\n        };\n        salts.push(salt);\n        index+=1;\n    }'
b='    let mut index=0usize;\n    while index<aspis_core::r0::FIBRE_COUNT {\n        salts=derive_private_salt_step(reserved,context,hash,tag,index as u32,salts)?;\n        index+=1;\n    }'
assert s.count(a)==1
p.write_text(s.replace(a,b)+'\nfn derive_private_salt_step(reserved:&ReservedStateOnlyAttemptSecrets,context:StateOnlyHidingContext,hash:HashFn,tag:u8,index:u32,mut salts:Vec<[u8;32]>)->Result<Vec<[u8;32]>,Error> {\n    let salt=reserved.derive_pool_v1_leaf_salt(hash,context,tag,index).map_err(|_|Error::Semantic)?;\n    salts.push(salt);\n    Ok(salts)\n}\n')
