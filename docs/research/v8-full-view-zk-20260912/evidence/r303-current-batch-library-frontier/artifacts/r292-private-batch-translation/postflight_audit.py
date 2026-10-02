#!/usr/bin/env python3
"""Audit saved R292 translation outputs only; does not invoke Lean/Aeneas."""
import hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
GEN=HERE/'generated'
SOURCE_SHA='999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5'
BINARY_SHA='63b04a88532b8fb0aaa0d274881b5cacf00bc4f449243ece905178f0de9cc495'
RUST_NAME='aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch'
LEAN_NAME='AspisR292PrivateBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((GEN/'translation.json').read_text())
entries=[f for f in manifest.get('functions',[]) if f.get('rust_name')==RUST_NAME and f.get('lean_name')==LEAN_NAME]
assert len(entries)==1, len(entries)
entry=entries[0]
assert entry['def_id']==0 and entry['is_local'] is True and entry['is_opaque'] is False
assert entry['source']=={'file':'../r110_norm.rs','begin_line':61,'end_line':69}
lean=GEN/entry['lean_file']
text=lean.read_text()
needle='def circle_norm.joined_inverse.line_norm.r110_norm.batch\n'
assert text.count(needle)==1, text.count(needle)
line=next(i for i,s in enumerate(text.splitlines(),1) if s==needle.strip())
func_template=GEN/'AspisR292PrivateBatch/FunsExternal_Template.lean'
type_template=GEN/'AspisR292PrivateBatch/TypesExternal_Template.lean'
func_text=func_template.read_text(); type_text=type_template.read_text()
func_holes=re.findall(r'^axiom\s+([^\s(]+)',func_text,re.M)
type_holes=re.findall(r'^axiom\s+([^\s(]+)',type_text,re.M)
assert len(func_holes)==5,func_holes
assert len(type_holes)==1,type_holes
log=(HERE/'translate.log').read_text()
warns=[line for line in log.splitlines() if '[Warn ]' in line]
result={
 'translator_exit_status':0,
 'root_emission':{
   'translation_manifest_entry_count':len(entries),'def_id':entry['def_id'],'rust_name':entry['rust_name'],
   'lean_name':entry['lean_name'],'lean_file':entry['lean_file'],'lean_definition_line':line,
   'source_span':entry['source'],'local':entry['is_local'],'opaque':entry['is_opaque'],
   'can_fail':entry['can_fail'],'can_diverge':entry['can_diverge'],'is_rec':entry['is_rec'],
   'manifest_entry_emitted':True,'Lean_definition_emitted':True},
 'unresolved_external_template_declarations':{
   'functions':func_holes,
   'types':type_holes,
   'status':'Generated template axioms remain holes; no template was filled/imported/compiled.'},
 'translator_warnings':warns,
 'resource_metrics':{'wall_time':'0:01.03','peak_rss_kib':143968,'swaps':0,'gnu_time_exit_status':0},
 'source_sha256':SOURCE_SHA,'binary_sha256':BINARY_SHA,'source_revision_recorded':'380c7d46c9719dcfcab601fac2607861d47dee02',
 'generated_sha256':{str(p.relative_to(HERE)):sha(p) for p in sorted(GEN.rglob('*')) if p.is_file()},
 'scope':'Saved-output audit only. Translation exited successfully and emitted batch; external template obligations remain. No Lean compile or proof/source-correspondence claim.'}
(HERE/'translation-result.json').write_text(json.dumps(result,indent=2)+'\n')
launch=json.loads((HERE/'launch.json').read_text())
run=HERE/'run.py'
launch['local_runner']=str(run)
launch['local_runner_sha256']=sha(run)
launch['reservation_before_observed']={'MemAvailable_kib':55215392,'R289_MemoryMax_bytes':7516192768,'R289_MemorySwapMax_bytes':0,'systemd_run_unit':'aspis-r292-private-batch-translation.service'}
(HERE/'launch.json').write_text(json.dumps(launch,indent=2)+'\n')
final={
 'translator_exit_status':0,'required_batch_root_emitted':True,
 'root_manifest_entry':entry,'root_lean_definition_line':line,
 'unresolved_external_function_template_count':len(func_holes),
 'unresolved_external_type_template_count':len(type_holes),
 'source_sha256':SOURCE_SHA,'binary_sha256':BINARY_SHA,'source_revision_recorded':'380c7d46c9719dcfcab601fac2607861d47dee02',
 'resource_metrics':result['resource_metrics']}
(HERE/'result.json').write_text(json.dumps(final,indent=2)+'\n')
print(json.dumps(final,indent=2))
