"""Produce a per-prerequisite h6 disposition, retaining failed checks explicitly."""
import json,pathlib,hashlib,collections
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume8'
rows=json.loads((E/'project-closure.json').read_text());mp={r['module']:r for r in rows};missing=json.loads((E/'prerequisites-before.json').read_text());envs=json.loads((E/'environment-fingerprints.json').read_text());own=envs['own']['objects'];other=envs['runjoin20']['objects'];ident=json.loads((E/'candidate-identity-check.json').read_text())['candidates'];builds=json.loads((E/'stream-b-build-records.json').read_text());copied=json.loads((E/'join-candidate-cache-manifest.json').read_text());endpoint=json.loads((E/'runjoin20-project-hash-check.json').read_text());ep={r['module'].replace('/','.'):r for r in endpoint}
ext=json.loads((E.parent/'resume7/external-object-manifest.json').read_text());extnames={r['module'].replace('/','.') for r in ext}
def closure(m):
 seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n)
  for d in mp.get(n,{}).get('imports',[]):visit(d)
 for d in mp[m]['imports']:visit(d)
 return seen
out=[]
for r in missing:
 m=r['module'];deps=closure(m);records=[b for b in builds if b.get('module',b.get('target','')).replace('/','.')==m and b['source_sha256']==r['sha256']]
 src=copied['objects'].get(m);candidates=ident[m]
 # Compare all transitive project imports, plus the entire h4 external cohort
 # (a strict superset of the transitive external imports).
 mismatch=[];unavailable=[]
 for d in sorted(deps|extnames):
  a=own.get(d);b=other.get(d)
  if a is None or b is None:unavailable.append(d)
  elif a['sha256']!=b['sha256']:mismatch.append(dict(module=d,own=a['sha256'],runjoin20=b['sha256']))
 # Successful Stream B receipts often record only direct dependencies. Check
 # those as well; never promote a direct-only fingerprint to a complete one.
 receipt_checks=[]
 for b in records:
  ds=b.get('dependency_object_hashes',{});problems=[]
  for d,h in ds.items():
   a=own.get(d.replace('/','.'))
   if a is None or a['sha256']!=h:problems.append(dict(module=d,recorded=h,own=a))
  receipt_checks.append(dict(branch=b['branch'],evidence=b['evidence_path'],attempt=b.get('attempt'),recorded_dependencies=len(ds),mismatches=problems,transitive_fingerprint_recorded=False))
 out.append(dict(module=m,selected_source=r,endpoint_669_contains_module=m in ep,source_check=dict(copied_manifest_source_match=bool(src and src.get('source_sha256')==r['sha256']),matching_source_successful_stream_b_receipts=[b['evidence_path'] for b in records],copied_manifest_origin=copied['cache_origin'] if src else None),dependency_check=dict(reference_environment='runjoin20',transitive_source_imports=sorted(deps),external_superset_count=len(extnames),mismatches=mismatch,unavailable_in_own_or_candidate=unavailable,complete_match=not mismatch and not unavailable,stream_b_receipt_checks=receipt_checks),environment_check=dict(own_environment='environment-fingerprints.json#own',candidate_environments='candidate-identity-check.json#'+m,toolchain_and_literal_prefix_match=any(c['toolchain_identical'] and c['lean_path_prefix_identical'] for c in candidates)),candidate_count=len(candidates),reusable=False,disposition='private build required: no candidate verified against all three h6 conditions'))
(E/'h6-prerequisite-dispositions.json').write_text(json.dumps(out,indent=2)+'\n')
summary=dict(prerequisites=len(out),endpoint_recorded_objects=len(endpoint),endpoint_overlap=sum(x['endpoint_669_contains_module'] for x in out),matching_source_B_build_records=sum(bool(x['source_check']['matching_source_successful_stream_b_receipts']) for x in out),without_B_build_record=sum(not x['source_check']['matching_source_successful_stream_b_receipts'] for x in out),candidate_source_copied_manifest_matches=sum(x['source_check']['copied_manifest_source_match'] for x in out),runjoin_transitive_comparisons_with_mismatches=sum(bool(x['dependency_check']['mismatches']) for x in out),runjoin_transitive_comparisons_with_missing_objects=sum(bool(x['dependency_check']['unavailable_in_own_or_candidate']) for x in out),literal_environment_matches=0,reused=0,remaining_private_builds=200,min_attempts_step1=201,available_attempts=100,audit_ids=[39997,39998,39999],compile_attempts=0,kani=0,ids_consumed=[])
(E/'h6-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));print('example mismatch',out[0]['dependency_check']['mismatches'][:4]);print('example missing',out[0]['dependency_check']['unavailable_in_own_or_candidate'][:4])
