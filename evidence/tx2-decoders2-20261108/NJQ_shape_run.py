from NJQ_native import *
from NJQ_patch import read_patch
mode=sys.argv[2];a=sys.argv[1];assert mode in ['positive','inverse','unimplied','modifies']
if mode!='positive':assert json.loads((E/'NJQ_K039/receipt.json').read_text())['exit_status']==0
text=read_patch('NJQ_identity_shape')
if mode=='modifies':text=text.replace('let control_writes=false;','let control_writes=true;')
target='shape_unimplied' if mode=='unimplied' else 'shape_contract'
fresh(a,'statement:pool_v1::format::NJQ_identity_shape::'+target,[('crates/aspis-statement/src/pool_v1/format.rs','NJQ_identity_shape',text)],mode=='inverse')
