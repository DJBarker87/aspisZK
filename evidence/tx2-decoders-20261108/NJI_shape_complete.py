from NJI_patch import read_patch,write_patch
from NJI_native import *
for i,name in [(50,'unimplied'),(51,'weak_proof'),(52,'real'),(53,'inverted_proof'),(54,'frame')]:
 fresh(f'NJI_K{i:03}','statement:pool_v1::verifier_registry::NJI_shape::'+name,[('crates/aspis-statement/src/pool_v1/verifier_registry.rs','NJI_shape',read_patch('NJI_shape'))])
