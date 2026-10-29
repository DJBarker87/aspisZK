from auditlib9 import *
paths=[('rw',R+'R1Z/PV_OWNM_V239.lean'),('rw','tools/pv-ownh-20261029/harness.rs'),('rw','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs'),('rw','tools/r1-cost-probe/src/bin/devnet_spend.rs'),('rw',R+'R1Z/PV_RunJoin_Deployed.lean'),('rw',R+'R1Z/PrivacyR1HeadlineDeployedReal.lean'),('runjoin',R+'R1Z/PV_RunJoin_PublishSkeleton54.lean'),('runjoin',R+'R1Z/PV_RunJoin_LinkR24Discharged54.lean'),('runjoin',R+'R1Z/PV_RunJoin_OracleBridge38.lean')]
paths += [('rw','evidence/pv-diag10-20261029/'+m+'.lean') for m in ['PV_DIAG10_FILE','PV_DIAG10_JSON_STDOUT','PV_DIAG10_ERROR_STDERR','PV_DIAG10_Links','PV_DIAG10_Operands','PV_DIAG10_Attempt']]
out=[]
for k,p in paths:
 s=read(k,p);assert s is not None,(k,p);out.append(dict(ref=k,path=p,sha256=hashlib.sha256(s.encode()).hexdigest(),source='manifest.json',declarations=re.findall(r'^\s*(?:theorem|def|structure)\s+(\S+)',s,re.M)))
s=read('rw','tools/pv-ownh-20261029/harness.rs');native=json.loads(read('rw','evidence/pv-ownh-20261029/native-result.json'));assert hashlib.sha256(s.encode()).hexdigest()==next(x['sha256'] for x in native['inputs'] if x['path'].endswith('/harness.rs'))
assert 'pool_v1_pair_forest_copy_active_rows_v1()' in s and 'pool_v1_pair_forest_copy_active_row_masks_v1()' in s
(P/'statement-witnesses9.json').write_text(json.dumps(dict(sources=out,harness_hash_and_original_root_calls_verified=True,scope='Full statement source snapshots, inspection only; no new Lean elaboration or proof.'),indent=1)+'\n');save();print('Full statement and harness sources',len(paths),'captured')
