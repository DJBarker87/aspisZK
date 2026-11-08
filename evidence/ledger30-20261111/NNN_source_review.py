"""Immutable revalidation of the merged native producers; no prover/extraction run."""
from pathlib import Path
import hashlib,json,re,subprocess,lzma
E=Path(__file__).resolve().parent;R=E.parent;S=R/'stage-wrap-20261111';W=R/'entry-wrap-20261111'
H=lambda b:hashlib.sha256(b).hexdigest()
def blob(p):return subprocess.check_output(['git','show','HEAD:'+str(p)])
p=S/'NMV_control_review.py';s=p.read_text().replace("(E/'NMV_CONTROL_RESUME.json').write_text(json.dumps(out,indent=2)+'\\n')","assert json.loads((E/'NMV_CONTROL_RESUME.json').read_text())==out").replace('print(json.dumps(out))','')
ns={'__file__':str(p)};exec(compile(s,'NNN immutable parent controls','exec'),ns);controls=ns['out']
# Check reply dependence and write-footprint failures explicitly, in the same frozen configuration.
window_controls=[]
for positive,negative,assertion in [('NMV_K035','NMV_K036','out.is_ok()'),('NMV_K035','NMV_K038','l.n == 10'),('NMV_K041','NMV_K042','out.is_ok()'),('NMV_K041','NMV_K044','l.copies == 1')]:
 rc=json.loads((S/negative/'receipt.json').read_text());assert rc['exit_status']==1
 log=lzma.decompress((S/negative/'stdout.log.xz').read_bytes());assert b'VERIFICATION:- FAILED' in log and ('Failed Checks: assertion failed: '+assertion).encode() in log and b'unwinding assertion'not in log
 for a in [positive,negative]:
  graph=json.loads((S/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen']
  assert json.loads((S/(a+'-lock-check.json')).read_text())['unchanged']
  assert not json.loads((S/(a+'-source-check.json')).read_text())['errors']
 assert json.loads((S/(positive+'-graph-check.json')).read_text())['all_crate_features']==json.loads((S/(negative+'-graph-check.json')).read_text())['all_crate_features']
 assert ns['artifact'](positive,'NMV_src/programs/r1-cost-probe/src/NMV_Fission.rs')==ns['artifact'](negative,'NMV_src/programs/r1-cost-probe/src/NMV_Fission.rs')
 window_controls.append(dict(positive=positive,negative=negative,expected_failure=assertion,exit_status=1,stdout_sha256=H(log),same_fission=True,frozen_graph_features_and_lock=True))
p=S/'NMV_fission.py';s=p.read_text().replace("err=(E.parent/'pc-helpers2-20261110/PCG_solana_program_error.rs.txt').read_text()","err=subprocess.check_output(['git','show','HEAD:evidence/pc-helpers2-20261110/PCG_solana_program_error.rs.txt'],text=True)")
s=s.replace("(E/'NMV_Fission.rs').write_text(out)","assert (E/'NMV_Fission.rs').read_text().strip()==out.strip()").replace("(E/'NMV_ASSOCIATIONS.json').write_text(json.dumps(results,indent=2)+'\\n')","assert json.loads((E/'NMV_ASSOCIATIONS.json').read_text())==json.loads(json.dumps(results))")
ns={'__file__':str(p)};exec(compile(s,'NNN immutable fission','exec'),ns);fission=ns
p=W/'NMW_validate_source.py';s=p.read_text().replace("(E/'NMW_SOURCE_AUDIT.json').write_text(json.dumps(report,indent=1)+'\\n')","prior=json.loads((E/'NMW_SOURCE_AUDIT.json').read_text()); assert {k:v for k,v in prior.items() if k!='extractions'} == {k:v for k,v in report.items() if k!='extractions'}; assert [{k:v for k,v in z.items() if k!='features'} for z in prior['extractions']] == [{k:v for k,v in z.items() if k!='features'} for z in report['extractions']]")
ns={'__file__':str(p)};exec(compile(s,'NNN immutable emitted bodies','exec'),ns)
# Confirm hash links, not just presence of a pin manifest.
links=[]
for label,attempt in [('process','NMW_E002'),('entry','NMW_E001')]:
 b=W/('NMW_'+label+'_emitted');pins=json.loads((b/'NMW_PINS.json').read_text());raw=b/'raw'/('NMW_'+label)/'Funs.lean';llbc=b/(label+'.llbc')
 rawll=llbc.read_bytes();assert H(rawll)==pins['llbc_sha256']
 # Extraction receipts and sources remain at historical revisions; existence alone is not a link.
 rp=W/attempt/'receipt.json';receipt=json.loads(rp.read_text());assert receipt['exit_status']==0;assert pins['manifest_sha256']==receipt['source_hashes']['NMW_STAGING_MANIFEST.json'];assert pins['candidate_sha256']==H(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/candidate.rs']))
 links.append(dict(emission=attempt,label=label,pins_sha256=H((b/'NMW_PINS.json').read_bytes()),receipt_sha256=H(rp.read_bytes()),raw_sha256=H(raw.read_bytes()),llbc_sha256=H(rawll),candidate_sha256=pins['candidate_sha256'],source_hashes=receipt.get('source_hashes',{}),fresh_parent_provenance=True,qualification='Frozen source audit, candidate/LLBC/output/tool pin chain retained; child emission provenance remains unresolved under(bk).'))
kmx=blob('evidence/kani-mitig-20261028/KMX_copy_stubs.patch');assert H(kmx)==controls['kmx_patch_sha256']
report=dict(status='PASS',fission_associations=fission['results'],fission_sha256=H((S/'NMV_Fission.rs').read_bytes()),fission_hash_linked=True,controls=controls,emitted_audit=ns['report'],fresh_parent_provenance=links,attempt_identity_correction='Actual receipts: NMW_E001 is entry; NMW_E002 is process (task labels reversed). Hash links checked against each actual receipt.',KMX_sha256=H(kmx),new_Kani=0,new_extraction=0,window_laws=['S2TrustedSdkBorrow','TrustedStd','RuntimeClockSlotBinding (including deployed owned.rs:479 Err arm, TGB-4)','RuntimeReturnDataClear'],TGB4='Reporting addition only, existing trust item; RowSpec_240 unchanged')
report['reply_and_footprint_controls']=window_controls
report['resolved_features_by_package_id']={label:{z['id']:z['features']for z in json.loads((W/('NMW_'+label+'_emitted/metadata.json')).read_text())['resolve']['nodes']}for label in ['process','entry']}
(E/'NNN_SOURCE_REVIEW.json').write_text(json.dumps(report,indent=1)+'\n');print('NNN immutable fission, controls and emitted-body pin chains PASS')
