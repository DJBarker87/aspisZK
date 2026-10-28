from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
scope=json.loads((E/'NDE_FRONTIER.json').read_text())
closed={
 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31':(2,3,'semantic_lift','every u32, including noncanonical words'),
 'crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31':(4,5,'copy_lift','every u32, including noncanonical words'),
 'crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs':(6,7,'extension_limbs','every four-word QM31 carrier, including noncanonical words')}
rows=[]
for f in sorted(set([r['representative'] for r in scope]+list(closed))):
 if f in closed:
  p,n,t,d=closed[f];r=dict(function=f,status='CLOSED',scope='local value bridge only; enclosing caller/physical association OPEN',domain=d,reference='NDE_reference.rs; E001 pins and source snapshots',extraction='NDE_E001',lean='NDE_LiftBridge.'+t,lean_attempt=3,positive=p,negative=n,copy_fidelity=[8,9],stubs='exact KMX copy_nonoverlapping; no arithmetic stubs, no function-pointer values',callee_domain='Actual frozen constructor bodies execute; no stub_verified callee used; constructors accept every word.')
 else:r=dict(function=f,status='OPEN',obstacle='Not attempted yet in this stage; pending independent native/reference and cohort-equality obligations.')
 rows.append(r)
(E/'NDE_LEDGER_DELTA.json').write_text(json.dumps(dict(schema=1,headline='AspisR1.RPx_Deployed.deployed',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',removes_trust=False,rows=rows),indent=2)+'\n')
lines=['# NDE frontier bridges','','All CLOSED labels below are local on the stated domain. The composed S2 and 100-bit target remain OPEN. Native contract semantic transport is the owner-approved P6/D188 trust reclassification, never removal.','','| Function | Status | Evidence / obstacle |','|---|---|---|']
for r in rows:lines.append('| `'+r['function']+'` | '+r['status']+' | '+(r.get('domain','')+'; '+r.get('lean','') if r['status']=='CLOSED' else r['obstacle'])+' |')
lines+=['','K002/K004/K006 pass; their exact inverted-contract controls K003/K005/K007 fail one intended ensures check each. Exact KMX pointer positive K008 passes and wrong-copy K009 fails one intended check. K001 is superseded by K002 (stricter copy/feature receipts), never counted twice. E001 extracted safe record references; L001/L002 compiled generated modules; L003 proves exact cohort equalities with standard axioms only. Constructor transport is bijective field placement, not byte-havoc. No stub_verified composition is used in this batch; no per-shape substitution credit is claimed.','','Deployed statement features: r0/pool-v1-kernel and all twelve optimized features, matching the isolated deployed verifier root. The statement-only Kani helper target omits no-entrypoint and has no program-entry credit. Core features exactly r0. Every graph-check from K002 includes isolated_deployed_features for every crate; workspace metadata is labelled over-unified and used only for frozen-graph identity. Scratch Cargo.lock is unchanged before/after every run, offline; exact KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.','','No repository crates/programs/ or existing Lean file changed. ELF rebuild trigger did not fire. Release pins remain inherited, not reproduced.']
(E/'NDE_FRONTIER_BRIDGES.md').write_text('\n'.join(lines)+'\n')
spec=json.load(open('evidence/native-compledger-20261028/NCZ_SUPPLEMENTAL.json'))
for f,(p,n,t,d) in closed.items():spec.append(dict(id='NDE::'+t,function=f,packet='native-front2-20261028',medium='Kani proof_for_contract plus failing control and exact KMX fidelity',reference_medium='NCO-pinned extraction plus cohort Lean equality',domain=d+'; local value bridge; no enclosing physical/native caller association. Theorem NDE_LiftBridge.'+t,positive=[p],negative=[n],shape_positive=[8],shape_negative=[9],lean=[3],reports=['NDE_FRONTIER_BRIDGES.md','NDE_LEDGER_DELTA.json','NDE_EXTRACTION_PINS.json'],additional_receipts=['evidence/native-front2-20261028/NDE_E001/receipt.json'],feature_status='DEPLOYED: isolated deployed root features and exact statement Kani features recorded in graph-check; target/ABI boundary retained',admit=True))
(E/'NDE_SUPPLEMENTAL.json').write_text(json.dumps(spec,indent=2)+'\n')
