from pathlib import Path
import textwrap
R=Path(__file__).resolve().parents[2];text=(R/'lean/JHd_Authentication.lean').read_text()
lines=text.splitlines()
common='''open Aeneas Aeneas.Std Result
open _root_.AdapterRw
'''
args=''' (ops : Ops)
    (verifier_program pool_program : solana_pubkey.Pubkey) (output_lane : U8) (current_slot : U64)
    (master_account checkpoint_account lane_account registry_account entry_account : r1_pool_adapter.owned.OwnedAccount)
    (val1 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (p : solana_pubkey.Pubkey)'''
for name,needle,extra in [
 ('MasterPda','let r8 ←',' (s2 : Slice (Slice U8))'),
 ('CheckpointRead','let r11 ←',''),
 ('MasterRegistry','let r10 ←',''),
 ('CheckpointDecoded','let a1 ← ops.op39 p','\n    (val4 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1)'),
 ('CheckpointPda','let r13 ←','\n    (val4 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (s6 : Slice (Slice U8))'),
 ('LaneDecoded','let a3 ←','\n    (val4 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (p2 : solana_pubkey.Pubkey)\n    (val7 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1)'),
 ('LaneRead','let r15 ←','\n    (val4 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (p2 : solana_pubkey.Pubkey)'),
 ('LanePda','let r17 ←','\n    (val4 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (p2 : solana_pubkey.Pubkey)\n    (val7 : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) (s10 : Slice (Slice U8))')]:
 start=next(i for i,l in enumerate(lines) if l.strip()==needle);indent=len(lines[start])-len(lines[start].lstrip());end=start+1
 while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>=indent):end+=1
 body=textwrap.dedent('\n'.join(lines[start:end])).rstrip()
 out='import JHi_Authentication\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JHj_'+name+'\n'+common
 out+='\n/-- Verbatim extracted authentication continuation; no successful leaf is installed. -/\ndef run'+args+extra+' :\n    Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError) := do\n'+textwrap.indent(body,'  ')+'\n#print axioms run\nend AspisR1.JHj_'+name+'\nend\n'
 (R/'lean'/('JHj_'+name+'.lean')).write_text(out)
