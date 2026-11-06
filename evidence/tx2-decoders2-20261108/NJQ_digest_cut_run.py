from NJQ_native import *
from NJQ_patch import read_patch
if len(sys.argv)>2:
 previous=sys.argv[1][:-3]+f"{int(sys.argv[1][-3:])-1:03d}"
 assert json.loads((E/previous/'receipt.json').read_text())['exit_status']==0
fresh(sys.argv[1],'statement:pool_v1::pair_forest_accounts::NJQ_digest_cut::digest_boundary',
 [('crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs','NJQ_digest_cut',read_patch('NJQ_digest_cut'))],len(sys.argv)>2)
