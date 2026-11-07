from pathlib import Path
import json,hashlib,re,subprocess,lzma
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
b=E/'NMX_auth_cut_emitted';pins=json.loads((b/'NMX_PINS.json').read_text())
assert pins['charon_exit']==pins['aeneas_exit']==pins['exit']==0
assert pins['lock_before']==pins['lock_after']
for p,h in pins['outputs'].items():assert sha((b/p).read_bytes())==h,p
assert json.loads((b/'NMX_GRAPH_CHECK.json').read_text())['graph_matches_frozen']
f=(b/'raw/NMX_auth/Funs.lean').read_text();s=f[f.index('def r1_pool_adapter.owned.authenticate_asq8_accounts\n'):f.rindex('end NMX_auth')]
n=json.loads((E/'NMX_NORMALIZATION.json').read_text())
for x,y in n['substitutions']:s=s.replace(x,y)
t=(E/'NMX_Emitted.lean').read_text();t=t[t.index('def auth '):t.index('\nend NMX_Emitted')]
assert re.sub(r'\s+','',s)==re.sub(r'\s+','',t)
assert not re.search(r'\b(loop|while)\b',f),'own body has loop; review bc'
# Exact frozen program body source is present in the transport payload.
manifest=json.loads((E/'NMX_STAGING_MANIFEST.json').read_text())
for p in ['Cargo.lock','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']:
 raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p]);assert sha(raw)==manifest['files'][p]['sha256']
md=json.loads((b/'metadata.json').read_text());pkgs={p['id']:p for p in md['packages']};nodes={p['id']:p for p in md['resolve']['nodes']}
root=next(i for i,p in pkgs.items() if p['name']=='aspis-r1-cost-probe-program');seen=set()
def visit(i):
 if i in seen:return
 seen.add(i)
 for d in nodes[i]['deps']:
  if any(k['kind'] in (None,'build') for k in d['dep_kinds']):visit(d['pkg'])
visit(root);assert all(pkgs[i]['name']!='aspis-pool' for i in seen)
report=dict(status='PASS',raw_sha256=sha(f.encode()),normalization='exact normalized root body after enumerated substitutions',canonical_equality='NMX_EmittedLinks.adopted (value/control only)',bc={'root':'no loops; all explicit returns and ? preserved as full Result/ControlFlow arms','transparent_own_getters_and_error_closures':'no loops','opaque_children':'CLOSED canonical owner audit reused; OPEN native217/234 remain separate packets','flagged_own_exits':[]},pool_revision='b936275465',pool_in_selected_closure=False,source_revision=manifest['revision'],features={pkgs[i]['name']:nodes[i]['features'] for i in seen},templates='archived, NEVER compiled; no template axiom credit')
(E/'NMX_SOURCE_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n');print('NMX source audit PASS')
