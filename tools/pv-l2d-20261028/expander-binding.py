"""Fail-closed structural inventory for the expander binding; no Kani credit.
This checks frozen body identity and feature-insensitivity of the selected
application bodies. It does not certify compiler/library lowering or the ROM.
"""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
sha=lambda b:hashlib.sha256(b).hexdigest()
freeze=json.loads((E/'expander-native-freeze.json').read_text())
features=json.loads((E/'deployed-client-features.json').read_text())
rows=[]
for r in freeze['bodies']:
 p=R/r['path'];s=p.read_text();a=s.index(r['start']);i=s.index('{',a)+1;depth=1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 b=s[a:i];assert sha(b.encode())==r['sha256'],r
 # cfg_attr(kani, ...) adds only verification contracts, not runtime bodies.
 assert not re.search(r'#\s*\[\s*cfg\s*\(|\bcfg!\s*\(|\bdebug_assert',b),r
 assert not re.search(r'#\s*\[\s*cfg_attr\s*\(\s*(?!kani\b)',b),r
 rows.append(dict(**r,selected_application_body_feature_invariant=True))
source=(R/'crates/aspis-prover/src/state_only_entropy.rs').read_text()
assert 'const PROFILE21_SOURCE_EXPAND_DOMAIN: &[u8] = b"aspis:state-only:profile21:source-expand:v1";' in source
assert 'pub const HOST_HASH: HashFn = host_hashv;' in (R/'crates/aspis-prover/src/lib.rs').read_text()
assert 'pub fn new(a: M31, b: M31) -> CM31 {\n        CM31 { a, b }\n    }' in (R/'crates/aspis-core/src/field.rs').read_text()
for name in ['ScalarPort','ScalarRender','ExpanderPort','ExpanderTrace','Read4','FourLimbs','CollectedTrace','TraceMass']:
 p=R/f'docs/research/v8-r0-zk-20261009/lean/PV_L2D_{name}.lean'
 assert p.read_bytes()==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
v=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),application_bodies=rows,
 artifact='tools/r1-cost-probe devnet_spend',features_command=features['command'],
 feature_graph_sha256=sha((E/'deployed-client-features.json').read_bytes()),
 lock_sha256=sha((R/'tools/r1-cost-probe/Cargo.lock').read_bytes()),profile='release, opt-level=3; debug assertions and overflow checks false for these application crates',toolchain='1.94.1',
 differences=[
 dict(native='next_word four-byte slice/try_into/unwrap',reference='four individual indexed bytes',law='PV_L2D_Read4.conversion_bytes, decode_same, last_word_offsets; total bounds from Fin8 and Fin4'),
 dict(native='cursor increment before byte loads',reference='cursor increment after byte loads',law='PV_L2D_ExpanderPort.next models source ordering; indices use the saved offset in both; no claim that the owned reference write-order trace equals native'),
 dict(native='while retry<16 with retry increment only after rejection',reference='for 0..16 with early return',law='PV_L2D_ScalarPort.complete_source / after_exact; PV_L2D_ScalarRender.trace_render records native retry guards, including exhaustion'),
 dict(native='CM31::new after limb2 and limb4',reference='record constructors after limb4',law='constructor is the checked exact two-field record; zero branch/index/loop events; PV_L2D_FourLimbs.complete_four retains all short-circuit errors'),
 dict(native='zeroize on Drop, then Zeroizing seed drop',reference='owned state retained by the finite checker',law='NOT PROVED: destruction excluded from current port model; retain as whole-row residual')],
 evidence_class='structural (K-1 substitute), partial binding inventory plus complete-Result owned laws and finite validation; NOT whole-row closure',
 retained=['native drop/zeroize and SHA/library internal observer', 'joint seed/attempt history with previous hash reads and publication', 'canonical successful-preparation association', 'installation in the concrete endpoint realRows/modelRows; no T addition'],
 nonvacuity='expander-v3 finite positive and matched negative controls, plus directed failures on each of four limbs; receipt must exist and pass before credit')
(E/'expander-structural-binding.json').write_text(json.dumps(v,indent=2)+'\n');print('checked',len(rows),'application body identities; whole row remains OPEN')
