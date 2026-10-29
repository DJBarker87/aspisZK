"""Exact frozen-lock graph projection for this lane's fixed feature selection.
No unlisted package or dependency-edge omission is accepted.
"""
import hashlib,json,subprocess,tomllib

def exact_graph(m,frozen):
 key=lambda p:(p['name'],p['version'],p.get('source'))
 f={key(p):p for p in frozen['package']};p={x['id']:x for x in m['packages']}
 actual={key(x) for x in m['packages']}
 inactive={'aspis-z4b-probe','aspis-r1-cert-build','aspis-r1-cert-check'}
 excluded={k for k in f if k[0] in inactive}
 assert len(excluded)==3
 expected=set(f)-excluded
 assert actual==expected,('package graph drift',actual-expected,expected-actual)
 edges={(key(p[n['id']]),key(p[d])) for n in m['resolve']['nodes'] for d in n['dependencies']}
 lock_edges=set()
 for k,q in f.items():
  if k not in expected:continue
  for label in q.get('dependencies',[]):
   b=label.split(' ')
   targets=[x for x in f if x[0]==b[0] and (len(b)<2 or x[1]==b[1]) and (len(b)<3 or x[2]==b[2].strip('()'))]
   assert len(targets)==1,(label,targets)
   if targets[0] in expected:lock_edges.add((k,targets[0]))
 # These are exactly the prover/r1p-check optional edges in the FROZEN manifest.
 cargo=tomllib.loads((__import__('pathlib').Path(__file__).parent/'NDM_src/crates/aspis-r1-cost-probe/Cargo.toml').read_text())
 disabled={'aspis-prover','sha2','serde_json','getrandom'}
 assert all(cargo['dependencies'][n]['optional'] is True for n in disabled)
 omitted={(a,b) for a,b in lock_edges if a[0]=='aspis-r1-cost-probe' and b[0] in disabled}
 assert len(omitted)==4
 n=next(n for n in m['resolve']['nodes'] if p[n['id']]['name']=='aspis-r1-cost-probe')
 assert not ({'prover','r1p-check'} & set(n['features']))
 expected_edges=lock_edges-omitted
 assert edges==expected_edges,('edge graph drift',edges-expected_edges,expected_edges-edges)
 canonical=dict(packages=sorted(actual,key=str),edges=sorted(edges,key=str))
 return dict(exact_frozen_selected_graph=True,package_count=len(actual),edge_count=len(edges),disabled_packages=sorted(excluded,key=str),disabled_optional_edges=sorted(omitted,key=str),canonical_graph_sha256=hashlib.sha256(json.dumps(canonical,sort_keys=True).encode()).hexdigest())
