from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;x=json.loads((H/'charon-003.json').read_text());cmd=x['command'];i=cmd.index('--consts');cmd[i+1]='initializers'
# Include the small literal initializers individually; avoid Aeneas' generic
# --consts values analysis crash. Deployment accessor bodies stay opaque.
consts=['aspis_r1_cost_probe::verifier::PROOF_BYTES','aspis_statement::pool_v1::pair_terminal::POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES','aspis_statement::pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC','aspis_statement::pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES','aspis_statement::pool_v1::pair_forest_terminal::POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES']
consts+=['crate::r1_pool_adapter::'+n for n in ['PROFILE_BINDING','RELEASE_BINDING','AUDIT_POLICY_BINDING','PAIR_FOREST_MASTER_SEED','PAIR_FOREST_LANE_SEED','PAIR_FOREST_CHECKPOINT_SEED','VERIFIER_REGISTRY_SEED','VERIFIER_ENTRY_SEED','VERIFIER_REGISTRY_V2_SEED','VERIFIER_ENTRY_V2_SEED']]
i=cmd.index('--dest-file');cmd[i:i]=[arg for n in consts for arg in ['--include',n]]
x.update(attempt='charon-004',command=cmd,change='Replace consts=values (Aeneas FunsAnalysis option None) with selective literal initializer inclusion; keep concrete enum layouts.')
(H/'charon-004.json').write_text(json.dumps(x,indent=2)+'\n')
