from pathlib import Path
import subprocess,tomllib,json
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def manifest(p):return tomllib.loads(subprocess.check_output(['git','show',rev+':'+p],text=True))
v=manifest('crates/aspis-r1-cost-probe/Cargo.toml');s=manifest('crates/aspis-statement/Cargo.toml');expected={'r0','pool-v1-kernel'}
for item in v['features']['optimized-terminal']:
 dep,feature=item.split('/');assert dep=='aspis-statement';expected.add(feature)
while True:
 extra={item for feature in expected for item in s['features'][feature] if '/' not in item}
 if extra<=expected:break
 expected|=extra
assert len(expected)==14
checked=[]
for p in sorted(E.glob('KNG_K*/receipt.json')):
 r=json.loads(p.read_text());features={n['name']:set(n['features']) for n in r['resolved_features_per_crate']}
 assert features['aspis-statement']==expected,p
 if 'aspis-r1-cost-probe' in features:assert features['aspis-r1-cost-probe']=={'default','private-leaf-salts','optimized-terminal','program-build'}
 assert features['aspis-core']=={'r0'}
 checked.append(r['attempt'])
(E/'KNG_FEATURE_AUDIT.json').write_text(json.dumps(dict(frozen_revision=rev,derived_from_frozen_manifests=True,expected_statement_features=sorted(expected),verifier_features=['default','private-leaf-salts','optimized-terminal','program-build'],core_features=['r0'],checked_receipts=checked),indent=2)+'\n')
print(len(checked),'receipt feature graphs match exact deployed closure')
