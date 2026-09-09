#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
h=Path(__file__).resolve().parent;r=h.parents[2]
assert str(r)=='/home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909' and not (r/'.git').exists()
p=r/'programs/aspis-pool/src/pair_forest.rs';s=p.read_text();assert 'process_checkpoint_receipt_v1' not in s
before=hashlib.sha256(s.encode()).hexdigest()
def function(name):
 start=s.index('pub '+('fn ' if name.startswith('plan') else '(crate) fn ')+name) if name.startswith('plan') else s.index('pub(crate) fn '+name)
 brace=s.index('{',start);level=1;end=brace+1
 while level:
  if s[end]=='{':level+=1
  elif s[end]=='}':level-=1
  end+=1
 return s[start:end]
planner=function('plan_pair_forest_checkpoint_accounts_v1').replace('plan_pair_forest_checkpoint_accounts_v1','plan_receipted_checkpoint_v1').replace('    checkpoint_account: &AccountInfo', '    receipts: &[AccountInfo<\'_>],\n    checkpoint_account: &AccountInfo').replace('decode_checkpoint_lanes_box_v1(program_id, master_account.key, lane_accounts)?','decode_checkpoint_receipted_lanes_v1(program_id, master_account.key, lane_accounts, receipts)?')
processor=function('process_pair_forest_checkpoint_with_runtime_v1').replace('process_pair_forest_checkpoint_with_runtime_v1','process_receipted_checkpoint_v1').replace('decode_pair_forest_checkpoint_instruction_v1(instruction_data)?;', 'if instruction_data != b"AS8K\\x01\\x08\\x01\\x00" { return Err(ProgramError::InvalidInstructionData); }').replace('require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT)?','require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT + 8)?').replace('plan_pair_forest_checkpoint_accounts_v1(program_id, master, lanes, checkpoint)?','plan_receipted_checkpoint_v1(program_id, master, lanes, &accounts[12..20], checkpoint)?')
added=(h/'checkpoint_receipts.rs').read_text()+'\n'+planner+'\n'+processor+'\n'
(h/'checkpoint_receipts_generated.rs').write_text(added)
s+='\n#[cfg(v8_checkpoint_receipts)]\ninclude!("../../../docs/research/v8-isolated-devnet-smoke-20260909/checkpoint_receipts_generated.rs");\n';p.write_text(s)
p2=r/'programs/aspis-pool/src/processor.rs';q=p2.read_text();anchor='    } else if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8C" {';assert q.count(anchor)==1
route=''
for magic,fn in [('AS8V','process_checkpoint_receipt_v1'),('AS8K','process_receipted_checkpoint_v1')]:
 route+='    } else if cfg!(all(v8_checkpoint_receipts, feature = "pair-forest-account-evidence")) && magic == b"'+magic+'" {\n        #[cfg(all(v8_checkpoint_receipts, feature = "pair-forest-account-evidence"))]\n        { crate::pair_forest::'+fn+'(program_id, accounts, instruction_data, &Rent::get()?, &mut runtime) }\n        #[cfg(not(all(v8_checkpoint_receipts, feature = "pair-forest-account-evidence")))]\n        unreachable!()\n'
q=q.replace(anchor,route+anchor);p2.write_text(q)
(h/'checkpoint-receipt-inputs.json').write_text(json.dumps({'pair_forest_before':before,'pair_forest_after':hashlib.sha256(s.encode()).hexdigest(),'processor_after':hashlib.sha256(q.encode()).hexdigest(),'generated_sha256':hashlib.sha256(added.encode()).hexdigest(),'configuration':'v8_checkpoint_receipts; defaults unchanged; AS8C and atomic terminal unchanged'},indent=2)+'\n')
