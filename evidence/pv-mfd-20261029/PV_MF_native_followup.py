"""Trace historical input uses to explicit later restoration authorities.
No native or Lean execution, and no validity is transferred between file versions.
"""
from pathlib import Path
import json,subprocess,hashlib
D=Path(__file__).resolve().parent;old=json.load(open(D.parent/'pv-mfc-20261029/native-chains.json'));files={};raws={}
def read(p):
 if p not in raws:
  raw=subprocess.check_output(['git','show','HEAD:'+p]);raws[p]=raw
  files[p]=dict(path=p,blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),sha256=hashlib.sha256(raw).hexdigest())
 return raws[p]
def support(ps):
 for p in ps:read(p)
 return ps
# Re-verify the later body pins, independently of any historical whole-tree inventory.
verified=[]
for p in ['evidence/pv-rdb2c-20261028/constructor-binding.json','evidence/pv-rdb2f-20261029/own1-binding.json']:
 for x in json.loads(read(p))['sources']:
  if not x['path'].startswith('crates/'):continue
  b=read(x['path']);assert hashlib.sha256(b).hexdigest()==x['sha256']
  verified.append(dict(binding=p,path=x['path'],sha256=x['sha256']))
for x in json.loads(read('evidence/pv-rdcd3-20261028/v260-project-source-result.json'))['bodies']:
 assert hashlib.sha256(read(x['path'])).hexdigest()==x['source_sha256']
 verified.append(dict(binding='evidence/pv-rdcd3-20261028/v260-project-source-result.json',path=x['path'],sha256=x['source_sha256']))
for p,h in json.loads(read('evidence/pv-b3p6-20261028/native226-resume-source-pins.json')).items():
 assert hashlib.sha256(read(p)).hexdigest()==h
 verified.append(dict(binding='evidence/pv-b3p6-20261028/native226-resume-source-pins.json',path=p,sha256=h))
for r in old['records']:
 if r['category']!='C':continue
 n=r['record'];p=r['input']['path']
 if n in [258,259]:
  chain=support(['tools/pv-b3p6-20261028/structural_resume226.py','evidence/pv-b3p6-20261028/native226-resume-source-pins.json','evidence/pv-b3p6-20261028/structural132-resume3.json','evidence/pv-b3p6-20261028/structural133.json'])
  why='Superseded aggregate harness snapshot. V243 explicitly finalizes against native226-resume-source-pins.json: its lib.rs pin is 8f3e41e0..., neither historical aggregate pin fdad4270... nor e39f0647.... Every final native226 pin matches HEAD. The structural checker reads owned226.rs/reference226.rs and the frozen semantic-terminal body; its finalization reads the later native pin map, not either aggregate inventory. V228 has its separate structural132-resume3 body/token and native/feature receipts; V229 uses the later ownh literal/singleton restoration. No historical aggregate lib.rs identity is transferred to those later packets.'
 elif 260<=n<=292:
  chain=support(['evidence/pv-rdb2c-20261028/REPORT.md','evidence/pv-rdb2c-20261028/constructor-binding.json','evidence/pv-rdb2c-20261028/box-lowering-binding.json','evidence/pv-rdcd3-20261028/rows/V260.md','evidence/pv-rdcd3-20261028/v260-project-source-result.json','evidence/pv-rdb2f-20261029/own1-binding.json','evidence/pv-op254-20261027/REPORT.md'])
  why='Historical batch2 source/configuration inventory or prover-side construction packet, superseded at the credited source-law boundary. Recount9 selects RDB2F original verifier sampler/caller laws (sampler.rs/transcript.rs/verifier.rs), RDB2C materialize/constructor (weights.rs/host_weights.rs/transport.rs/state_only_prefix.rs plus explicit allocator/Box lowering), RDCD3 raw weights (weights.rs/transport.rs/opening.rs and field/table bodies), and B1 original powers selected callback. The fresh application pins in the RDB2F/RDB2C/RDCD3 packets match HEAD mechanically. The old prover.rs constructor/materialization packets are not the current weights.rs own-1 binding. Other inventory entries are whole-tree build context, not selected body laws. B1 retains native installation/caller/RunJoin as an obligation rather than using these old prover inventory entries to discharge it. This disposition excludes the historical evidence use; it does not certify a new caller or transfer an old source pin.'
 else:
  assert 295<=n<=305
  chain=support(['evidence/pv-cb3-20261026/RESUME6_ROWS.md','evidence/pv-cb3-20261026/RESUME6_FINAL_REPORT.md','tools/pv-cb3-20261026/arbitrary_bytes.rs','tools/pv-cb3-20261026/kani-lib.rs','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_Op246Source.lean','evidence/pv-rdcd-20261028/REPORT.md'])
  why='Collateral resume6 whole-tree identity, not an input body for the retained source-law closures. Trace the retained checks: unrestricted V195 invokes WideExact.to_le_bytes/owned wide_bytes_flat; V219 invokes state_only_sumcheck::state_only_boundary_sum/owned boundary_flat; V254 extraction explicitly imports multiproof::binary_parent and the abstract Digest32 callback. None of these eleven records is the core wide_exact/field/sumcheck body, multiproof body, owned P6 reference, or generation receipt consumed by those laws. The listed builder-reference files and host semantic/prover/sim/transcript/lib/dense/commitment snapshot paths occur in the broad support inventory, alongside failed/reference-only gates. V246 is subsequently replaced by the RDCD complete statement bridge; V242 is uncredited. No freshness/closure credit for these collateral snapshot entries is inferred from the historical resume6 manifest.'
 r.update(category='B',reason=why,review3_chain=chain,result='NOT APPLICABLE',disposition='historical/superseded evidence use; no pin migration')
(D/'native-chains.json').write_text(json.dumps(dict(records=old['records'],evidence_files=list(files.values()),current_body_pins_verified=verified,method='Exact original pointer retained; distinguish superseded whole-tree inventory from later explicit body/configuration restoration and retained native caller obligations.'),indent=2)+'\n')
print('native followup: 46 exclusions; prior 12 retained')
