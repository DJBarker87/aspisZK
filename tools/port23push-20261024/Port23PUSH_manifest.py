#!/usr/bin/env python3
"""Own job ledger. Never edits shared counters or counts historical receipts anew."""
import pathlib,json,hashlib,subprocess
R=pathlib.Path(__file__).resolve().parents[2]; E=R/'evidence/port23push-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=[]; extraction=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text());lean.append({k:j[k] for k in ['attempt','module','source_revision','source_sha256','deps_fingerprint','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']})
 lean[-1].update(receipt=str(p.relative_to(R)),receipt_sha256=sha(p))
 if j['exit_status']==0:
  assert all('sorryAx' not in line for line in j['print_axioms'])
for p in sorted(E.glob('extract-*/receipt.json')):
 j=json.loads(p.read_text()); extraction.append({k:j[k] for k in ['attempt','kind','command','source_revision','exit_status','wall_seconds','peak_aggregate_rss_bytes','cgroup_memory_peak_bytes','peak_observed_swap_bytes','limits','print_axioms']})
 extraction[-1].update(receipt=str(p.relative_to(R)),receipt_sha256=sha(p))
assert len(lean)<=13 and len(extraction)<=2
artifacts={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(E.rglob('*')) if p.is_file() and p.name!='manifest.json'}
assert all(v['bytes']<=5000000 for k,v in artifacts.items() if k.endswith('.json'))
out=dict(schema='Port23PUSH-own-ledger-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),entry_global_soundness='320/368 assigned; concurrent global usage is lead-owned',
 usage=dict(lean=len(lean),lean_limit=13,extraction=len(extraction),extraction_limit=2,kani=0,standalone_rust=0,backend=0,full_manifest=0),
 lean=lean,extraction=extraction,artifacts=artifacts,
 no_deployed_identity_gate=True,actual_mutable_owned_equality=False,effect_consumer_installed=False,
 missing_evidence='Early lean-001..004 receipts have inherited direct source/dependency/tool hashes and go checks, but not the explicit post/sysroot snapshot added for lean-005..006. No retrospective pre/post claim.',
 non_compiler_admission_failures=[dict(target='Port23PUSH_Frame initial dependency preflight',reason='unused S7Kani2OwnedPush object absent from inherited path; no compiler invoked, unused import removed')],
 source_assessment='Unchanged base source spans; new exact mutable extraction. Prior S7 content proofs/evidence only reused within their literal old scope; no fresh native/release association.')
(E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(usage=out['usage'],lean=[dict(target=j['module'],exit=j['exit_status'],wall=j['wall_seconds'],rss=j['peak_rss_bytes']) for j in lean],extraction=[dict(kind=j['kind'],exit=j['exit_status'],wall=j['wall_seconds']) for j in extraction])))
