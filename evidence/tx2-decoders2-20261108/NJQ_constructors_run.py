from NJQ_native import *
from NJQ_patch import read_patch
# A matched control is launched only after its positive scope passed.
if len(sys.argv)>3:
 previous=sys.argv[1][:-3]+f"{int(sys.argv[1][-3:])-1:03d}"
 receipt=E/previous/'receipt.json'
 assert receipt.is_file() and json.loads(receipt.read_text())['exit_status']==0, 'No control after a failed/timed-out positive; isolate first'
fresh(sys.argv[1],'statement:pool_v1::pair_forest_accounts::NJQ_constructors::'+sys.argv[2],
 [('crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs','NJQ_constructors',read_patch('NJQ_constructors'))],len(sys.argv)>3)
