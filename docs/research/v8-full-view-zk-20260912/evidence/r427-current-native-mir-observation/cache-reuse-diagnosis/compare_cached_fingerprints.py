#!/usr/bin/env python3
"""Strictly compare saved parent/candidate proc-macro2 cache evidence."""
import json,pathlib,sys
base=pathlib.Path(__file__).resolve().parent
meta=json.loads((base/'fingerprint-metadata.stdout.json').read_text())
parents={r['path']:r for r in meta['roots']['parent']['artifacts']}
candidates={r['path']:r for r in meta['roots']['candidate']['artifacts']}
shared=sorted(set(parents)&set(candidates))
checks=[]
for rel in shared:
 a,b=parents[rel],candidates[rel]
 checks.append({'path':rel,'parent_sha256':a['sha256'],'candidate_sha256':b['sha256'],'equal':a['sha256']==b['sha256'] and a['bytes']==b['bytes']})
new=sorted(set(candidates)-set(parents));missing=sorted(set(parents)-set(candidates))
assert not missing,missing
assert all(x['equal'] for x in checks),[x for x in checks if not x['equal']]
new_fingerprint=[x for x in new if 'proc-macro2-f18635ddfd7f68bb' in x]
assert new_fingerprint==['release/.fingerprint/proc-macro2-f18635ddfd7f68bb/invoked.timestamp'],new_fingerprint
assert len(checks)>0
report={'status':'parent cache artifacts and fingerprint metadata are byte-identical in the candidate; interrupted candidate-only fingerprint artifact recorded','shared_artifact_count':len(checks),'shared_artifacts_all_equal':True,'candidate_only_paths':new,'parent_only_paths':missing,'proc_macro2_cached_library_json':parents['release/.fingerprint/proc-macro2-b731dd505951052a/lib-proc_macro2.json']['json'],'charon_driver_cached_fingerprint_json':[x['json'] for x in parents.values() if x['path'].endswith('/bin-charon-driver.json')],'interpretation_boundary':'The cache comparison confirms copied artifacts match their parent copies. Cargo nevertheless selected a new proc-macro2 fingerprint variant; its directory has only invoked.timestamp, so expected feature/profile/rustflag values were not written. Saved evidence does not identify why Cargo selected that unit. No Cargo rerun/build is authorized here.'}
(base/'fingerprint-comparison.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({'shared_artifact_count':len(checks),'candidate_only_paths':new,'proc_macro2_features':report['proc_macro2_cached_library_json']['features'],'proc_macro2_profile':report['proc_macro2_cached_library_json']['profile'],'proc_macro2_rustflags':report['proc_macro2_cached_library_json']['rustflags'],'charon_driver_profile':[x['profile'] for x in report['charon_driver_cached_fingerprint_json']],'charon_driver_rustflags':[x['rustflags'] for x in report['charon_driver_cached_fingerprint_json']]},indent=2))
