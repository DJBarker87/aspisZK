#!/usr/bin/env python3
"""Pinned source inspection, not formal certification of runtime/SDK lowering."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
R=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
files={'entrypoint':R/'solana-program-entrypoint-2.3.0/src/lib.rs','account':R/'solana-account-info-2.3.0/src/lib.rs','serializer':R/'solana-program-runtime-4.2.1/src/serialization.rs','instruction':R/'solana-transaction-context-4.2.1/src/instruction.rs'}
anchors={'entrypoint':['let data = Rc::new(RefCell::new({','accounts.push(accounts[dup_info as usize].clone());','deserialize_account_info(input, offset)'], 'account':['pub data: Rc<RefCell<&\'a mut [u8]>>'], 'serializer':['.is_instruction_account_duplicate(instruction_account_index)','SerializeAccount::Duplicate(index)'], 'instruction':['None` if it is the first account with this key','self.get_index_of_account_in_instruction(index_in_transaction)?']}
rows={}
for name,p in files.items():
 s=p.read_text();found={a:s[:s.index(a)].count('\n')+1 for a in anchors[name]}
 rows[name]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'anchors':found}
 (H/('runtime-'+name+'.rs.txt')).write_text(s)
result={'premise':'AspisR1.AdapterRw.RuntimeEntrypointAdmission','source_check':rows,'scope':'source inspection only; runtime/SDK interpretation retained as named premise independent of acceptance','derivation':['deserialize_account_info creates fresh Rc<RefCell> for each nonduplicate record','RefCell::new starts unborrowed; deserialize returns with no guards','duplicate instruction account = earlier occurrence of same transaction account/key','SDK duplicate branch clones AccountInfo, hence Rc data cell identity','normal runtime serialization partitions separate account byte allocations; no external SDK borrows enter program memory'],'runtime':'measurement runtime Agave 4.2.1 / LiteSVM 0.16.0; production SDK entrypoint 2.3.0 pinned by Cargo.lock','restriction_on_account_bytes_keys_owners_flags_lengths':False,'allocation_and_CU':'separate runtime/resource gates; not part of this premise','print_axioms':'N/A: source inspection'}
(H/'runtime-source-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(rows,indent=2))
