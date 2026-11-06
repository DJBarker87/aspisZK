from NJI_patch import read_patch,write_patch
from NJI_native import *
for i,name in [(45,'weak_proof'),(46,'real'),(47,'unimplied'),(48,'inverted_proof'),(49,'frame')]:
 fresh(f'NJI_K{i:03}','statement:pool_v1::verifier_registry::NJI_shape::'+name,[('crates/aspis-statement/src/pool_v1/verifier_registry.rs','NJI_shape',read_patch('NJI_shape'))])
