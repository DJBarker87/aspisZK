from KNC_host import *
import sys
name=sys.argv[1]
s=(E/'KNC_MINIMAL.rs.txt').read_text()
module='NBZ_native';harness='NBZ_return_carriers'
if name=='some_false':s=s.replace('assert!(obs.is_none());','assert!(obs.is_some());')
elif name=='payload_false':s=s.replace('assert_eq!(i,NBZ_Q);','assert!(i >= 10);')
elif name=='module_only':module='KNC_native'
elif name=='function_only':s=s.replace(harness,'KNC_return_carriers');harness='KNC_return_carriers'
elif name=='helper_only':s=s.replace('NBZ_mark_none','KNC_mark_none')
elif name=='globals_only':s=s.replace('NBZ_Q','KNC_Q').replace('NBZ_MARK_CALLS','KNC_MARK_CALLS')
elif name!='baseline':raise SystemExit('unknown variant')
(E/('KNC_variant_'+name+'.rs.txt')).write_text(s)
admit('KNC_UPLOAD_'+name)
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r});p=b/'KNC_src/crates/aspis-r1-cost-probe/src'
frozen=Path('/home/dombarker/project-offloads/codex-cx-kani-diag2-20261028/KNB_K008/sources/KNB_src/crates/aspis-r1-cost-probe/src/candidate.rs').read_text()
# Rename only the module identifier; keep the NBZ_native.rs file placement.
if {module!r}!='NBZ_native':
 assert 'mod NBZ_native;' in frozen
 frozen=frozen.replace('mod NBZ_native;', 'mod '+{module!r}+';')
(p/'candidate.rs').write_text(frozen)
(p/'NBZ_native.rs').write_text({s!r})
print(json.dumps(dict(variant={name!r},module={module!r},harness={harness!r},source_sha256=hashlib.sha256((p/'NBZ_native.rs').read_bytes()).hexdigest(),candidate_sha256=hashlib.sha256((p/'candidate.rs').read_bytes()).hexdigest())))
''')
(E/('KNC_UPLOAD_'+name+'.json')).write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');assert r.returncode==0,r.stderr
print('verifier::candidate::'+module+'::'+harness)
