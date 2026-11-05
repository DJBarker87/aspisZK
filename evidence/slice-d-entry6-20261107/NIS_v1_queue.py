from NIS_native import *
s=''.join(l[1:] for l in (E/'NIS_v1.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
for i,name in enumerate(['validate_registry','validate_registry_wrong','validate_entry','validate_entry_wrong','decode_registry','decode_registry_wrong','decode_entry','decode_entry_wrong'],58):
 r=fresh('NIS_K%03d'%i,'statement:pool_v1::verifier_registry::NIS_v1::'+name,[('crates/aspis-statement/src/pool_v1/verifier_registry.rs','NIS_v1',s)])
 if r['exit_status'] not in [0,1]:break
