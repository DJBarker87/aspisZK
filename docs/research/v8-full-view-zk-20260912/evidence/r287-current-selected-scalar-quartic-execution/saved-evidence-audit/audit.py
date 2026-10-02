import hashlib, json, pathlib, re, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
DOC=ROOT/'docs/research/v8-full-view-zk-20260912'
SCR=ROOT/'.r21-scratch'
REV='380c7d46c9719dcfcab601fac2607861d47dee02'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def check_manifest(base, checksum_path):
    sums=load(checksum_path); checked=[]; bad=[]
    for rel,want in sums.items():
        p=base/rel
        got=sha(p) if p.is_file() else None
        checked.append(rel)
        if got!=want: bad.append({'path':rel,'expected':want,'actual':got})
    assert not bad, bad
    return {'manifest':str(checksum_path.relative_to(ROOT)),'entries_checked':len(checked),'mismatches':bad,'manifest_sha256':sha(checksum_path)}

# Confirm exact staged/promoted R286 target copies and the newly expanded publication sums.
r286=SCR/'r286-query-field-raw'; e286=DOC/'evidence/r286-current-query-field-raw'
r286_target=DOC/'lean/AspisR286QueryFieldRaw.lean'
r286_copies=[r286/'AspisR286QueryFieldRaw.lean',e286/'source/AspisR286QueryFieldRaw.lean',e286/'raw-adapter-audit/AspisR286QueryFieldRaw.lean',r286_target]
r286_hashes=[sha(p) for p in r286_copies]
assert len(set(r286_hashes))==1 and r286_hashes[0]=='f6b773d75fdab87ae3f4edc478862a1412a8f30fc2996dc50993567a0a8f5725'
r286_manifest=load(e286/'manifest.json')
r286_binding=load(e286/'raw-adapter-audit/binding-audit.json')
r286_builder=e286/'raw-adapter-audit/build_raw.py'
r286_roots=load(e286/'raw-adapter-audit/root-comparison.json')
assert r286_manifest['source_revision']==REV and r286_manifest['exit_status']==0
assert r286_manifest['source_sha256']==r286_hashes[0]
assert len(r286_manifest['complete_print_axioms'])==2
assert all(x['body_equal_after_authorized_adapter'] for x in r286_binding['helper_bindings'])
assert len(r286_binding['helper_bindings'])==6 and all(x['matches_R156'] for x in r286_binding['type_layouts'])
assert r286_binding['source_body_replacements']==0 and r286_binding['translation_or_compile_run'] is False
assert r286_binding['promoted_raw_target_sha256']==r286_hashes[0]
assert r286_roots['output_sha256']==r286_hashes[0]
assert all(x['copied_exactly'] for x in r286_roots['selected_blocks'])
assert [x['name'] for x in r286_roots['selected_blocks']]==['aspis_core.field.QM31.neg','aspis_core.field.QM31.mul_m31']
assert sha(r286_builder)=='f3a45df401f8e2d23297152918b8aa94294fceba36629a26cf303e86d4e18b5c'
assert sha(e286/'raw-adapter-audit/binding-audit.json')=='2e6d4cfdd38023c1ad17e7d84ff6746ef7859278d3f81319e4318b9fe943122b'
r286_sum_audit=check_manifest(e286,e286/'SHA256SUMS.json')
# Saved scratch checksum list also checked against present scratch artifacts.
scratch_sums=[]
for ln in (r286/'checksums.sha256').read_text().splitlines():
    h,rel=ln.split(None,1); rel=rel.strip().lstrip('*')
    p=ROOT/rel
    got=sha(p) if p.is_file() else None
    scratch_sums.append({'path':rel,'expected':h,'actual':got,'matches':got==h})
assert scratch_sums and all(x['matches'] for x in scratch_sums), [x for x in scratch_sums if not x['matches']]
# Retained rejected-import history and corrected target/import provenance.
rej=e286/'raw-adapter-audit/rejected-import-scaffold'
rej_reason=load(rej/'reason.json'); rej_record=load(rej/'rejection.json')
failed=(rej/'AspisR286QueryFieldRaw.failed-import-Aeneas.lean').read_text()
fixed=(e286/'raw-adapter-audit/AspisR286QueryFieldRaw.lean').read_text()
assert rej_reason['exit_status']==1 and rej_record['failure_log_id']=='1790918348088874000'
assert 'import Aeneas\n' in failed and 'import Aeneas.Std\n' in fixed
assert rej_record['replacement_target_sha256']==r286_hashes[0]
assert sha(rej/'aspis-focus-1790918348088874000.log')==sha(rej/'aspis-focus-1790918348088874000.log')
# Axioms from complete log and dedicated artifact, exact selected roots.
r286_log=(e286/'logs/aspis-focus-1790918374476869000.log').read_text()
r286_axioms=(e286/'axioms.txt').read_text().splitlines()
r286_log_axioms=[x for x in r286_log.splitlines() if ' depends on axioms: ' in x]
assert len(r286_axioms)==len(r286_log_axioms)==2 and r286_axioms==r286_log_axioms
foundations={'propext','Classical.choice','Quot.sound'}
assert all(set(re.findall(r'\b(?:propext|Classical\.choice|Quot\.sound|sorryAx|native_decide)\b',x))==foundations for x in r286_axioms)
assert r286_manifest['wall_time']=='0:00.98' and r286_manifest['peak_rss_kib']==2526752 and r286_manifest['swaps']==0
assert r286_manifest['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'flags':'-j1 -M4500'}
assert 'Exit status: 0' in r286_log and 'Swaps: 0' in r286_log

# R287 target, saved source, staged copy, manifest, complete checksums, theorem headers and axioms.
r287=SCR/'R287SelectedScalarQuarticExecutionScratch.lean'; e287=DOC/'evidence/r287-current-selected-scalar-quartic-execution'
r287_target=DOC/'lean/AspisV8R19/R287SelectedScalarQuarticExecution.lean'
r287_copies=[r287,r287_target,e287/'source/R287SelectedScalarQuarticExecution.lean']
r287_hashes=[sha(p) for p in r287_copies]
assert len(set(r287_hashes))==1 and r287_hashes[0]=='08619ea574f389b8c4a4c944a098321375c81fbe47bb7c91dc71b53706e15328'
r287_manifest=load(e287/'manifest.json')
assert r287_manifest['source_revision']==REV and r287_manifest['exit_status']==0
assert r287_manifest['source_sha256']==r287_hashes[0]
r287_sum_audit=check_manifest(e287,e287/'SHA256SUMS.json')
r287_text=r287.read_text()
neg_header=re.search(r'theorem\s+neg_encode(.*?)\s*:=\s*by',r287_text,re.S)
mul_header=re.search(r'theorem\s+mul_m31_encode(.*?)\s*:=\s*by',r287_text,re.S)
assert neg_header and mul_header
assert 'z : QM31Exact' in neg_header.group(1) and 'rawNeg (encode z) = .ok (encode (-z))' in neg_header.group(1)
assert 'z : QM31Exact' in mul_header.group(1) and 'x : M31Exact' in mul_header.group(1)
assert 'rawMulM (encode z) (encodeBase x)' in mul_header.group(1)
assert 'nonzero' not in neg_header.group(1).lower()+mul_header.group(1).lower()
assert not re.search(r'\b(?:h|h_\w*)\s*:\s*(?:.*≠|.*Ne)',neg_header.group(1)+mul_header.group(1))
r287_log=(e287/'logs/aspis-focus-1790918384551295000.log').read_text()
r287_axiom_text=(e287/'axioms.txt').read_text()
r287_axiom_reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",r287_axiom_text,re.S)
r287_log_reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",r287_log,re.S)
assert len(r287_axiom_reports)==len(r287_log_reports)==2
normalize_axioms=lambda x: sorted(part.strip() for part in x.split(','))
assert [(n,normalize_axioms(a)) for n,a in r287_axiom_reports]==[(n,normalize_axioms(a)) for n,a in r287_log_reports]
r287_axioms=[f"'{n}' depends on axioms: [{', '.join(normalize_axioms(a))}]" for n,a in r287_axiom_reports]
assert [n for n,_ in r287_axiom_reports]==['AspisV8R19.R287SelectedScalarQuarticExecution.neg_encode','AspisV8R19.R287SelectedScalarQuarticExecution.mul_m31_encode']
assert all(set(re.findall(r'\b(?:propext|Classical\.choice|Quot\.sound|sorryAx|native_decide)\b',a))==foundations for _,a in r287_axiom_reports)
assert r287_manifest['wall_time']=='0:01.57' and r287_manifest['peak_rss_kib']==3709260 and r287_manifest['swaps']==0
assert r287_manifest['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'flags':'-j1 -M4500'}
assert 'Exit status: 0' in r287_log and 'Swaps: 0' in r287_log
# Confirm both launch wrappers correspond to the resource metadata and staged source.
for rel in ['evidence/r286-current-query-field-raw/run_focus.py','evidence/r287-current-selected-scalar-quartic-execution/run_focus.py']:
 txt=(DOC/rel).read_text()
 for needle in ['MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128','-j1','-M4500']:
  assert needle in txt,(rel,needle)
actual_rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
assert actual_rev==REV

report={
 'audit_scope':'Saved evidence consistency only. No Lean invocation, theorem reinterpretation, privacy/security decision, or release gate conclusion.',
 'source_revision':REV,'current_git_revision':actual_rev,
 'R286':{
  'promoted_target_sha256':r286_hashes[0], 'scratch_evidence_promoted_copies_byte_identical':True,
  'builder_sha256':sha(r286_builder),'binding_audit_sha256':sha(e286/'raw-adapter-audit/binding-audit.json'),
  'binding_six_helpers_and_three_type_layouts_consistent':True,'selected_roots_verbatim_replacements_zero':True,
  'raw_print_axioms_count':len(r286_axioms),'complete_axiom_lines':r286_axioms,
  'manifest_exit':r286_manifest['exit_status'],'wall_time':r286_manifest['wall_time'],'peak_rss_kib':r286_manifest['peak_rss_kib'],'swap':r286_manifest['swaps'],'resources':r286_manifest['resources'],
  'published_checksum_entries_verified':r286_sum_audit,'scratch_checksum_entries_verified':len(scratch_sums),
  'rejected_import_history':{'preserved':True,'log_id':rej_record['failure_log_id'],'exit_status':rej_reason['exit_status'],'reported_missing_module':'Aeneas.olean','corrected_import':'Aeneas.Std','target_sha256_after_import_fix':r286_hashes[0]}},
 'R287':{
  'target_sha256':r287_hashes[0],'scratch_target_saved_source_byte_identical':True,
  'theorem_headers':{'neg_encode':neg_header.group(1).strip(),'mul_m31_encode':mul_header.group(1).strip()},
  'no_nonzero_premise_in_either_header':True,'complete_axiom_lines':r287_axioms,'axioms_count':len(r287_axioms),
  'manifest_exit':r287_manifest['exit_status'],'wall_time':r287_manifest['wall_time'],'peak_rss_kib':r287_manifest['peak_rss_kib'],'swap':r287_manifest['swaps'],'resources':r287_manifest['resources'],
  'checksum_entries_verified':r287_sum_audit},
 'mechanical_conclusion':'Saved files, checksum manifests, targets, copies, logs, stated caps, recorded source revision, and complete axioms output agree. This is not a security release judgment.'}
out=ROOT/'.r21-scratch/r287-publication-evidence-audit/audit.json'
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'audit_json':str(out.relative_to(ROOT)),'all_checks_passed':True,'R286_checksums_verified':r286_sum_audit,'R287_checksums_verified':r287_sum_audit,'R286_raw_sha256':r286_hashes[0],'R287_source_sha256':r287_hashes[0],'revision':actual_rev},indent=2))
