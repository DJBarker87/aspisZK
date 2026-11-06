from NJI_native import fresh,E
import lzma
jobs=[(23,'master_cut','cut',False),(24,'master_cut','cut',True),(25,'policy_cut','cut',False),(26,'policy_cut','cut',True),(27,'entry_cut','cut',False),(28,'entry_cut','cut',True),(29,'registry_cut','cut',False),(30,'registry_cut','cut',True),(31,'master_cut','any_step',False),(32,'master_cut','any_step',True),(33,'checkpoint_step','step',False),(34,'checkpoint_step','step',True)]
for n,module,harness,wrong in jobs:
 parent='pair_forest_accounts' if module.startswith(('master','checkpoint')) else 'format' if module.startswith('policy') else 'verifier_registry'
 name='NJI_'+module;a='NJI_K%03d'%n
 rc=fresh(a,'statement:pool_v1::'+parent+'::'+name+'::'+harness,[('crates/aspis-statement/src/pool_v1/'+parent+'.rs',name,(E/(name+'.rs')).read_text())],invert=wrong)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 expected=1 if wrong else 0
 assert rc['exit_status']==expected and ('VERIFICATION:- FAILED' if wrong else 'VERIFICATION:- SUCCESSFUL') in log,(a,'not expected semantic verdict')
 assert 'unwinding failures' not in log and 'Timed out' not in log,(a,'excluded incomplete result')
