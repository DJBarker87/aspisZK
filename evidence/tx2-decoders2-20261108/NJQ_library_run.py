from NJQ_native import *
from NJQ_patch import read_patch
fresh(sys.argv[1],'statement:pool_v1::format::NJQ_library::'+sys.argv[2],
 [('crates/aspis-statement/src/pool_v1/format.rs','NJQ_library',read_patch('NJQ_library'))],len(sys.argv)>3)
