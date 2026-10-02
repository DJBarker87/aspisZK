#!/usr/bin/env python3
"""Build an inventory of saved R298/R300 evidence; performs no builds or translations."""
import hashlib, json
from pathlib import Path
A=Path(__file__).resolve().parent
ROOT=A.parents[1]
SRC=ROOT/'.r21-scratch'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
r298=SRC/'r298-slice-last-inventory'; r300=SRC/'r300-slice-last-translation'
inv=load(r298/'inventory.json'); audit=load(r298/'projection-audit.json')
res=load(r300/'result.json'); tr=load(r300/'translation-result.json'); cmd=load(r300/'translate-command.json')
correction=load(r300/'revision-correction.json')
files=[]
for p in sorted((A/'artifacts').rglob('*')):
 if p.is_file(): files.append({'path':str(p.relative_to(A)),'size_bytes':p.stat().st_size,'sha256':sha(p)})
manifest={
 'candidate':'R308 Slice.last publication candidate; for lead review only, not staged/committed/published.',
 'current_actual_repository_revision':'04d7d1b635ddb7c9af2ee3e2df3cdb68ae68bb43',
 'revision_reconciliation':{
  'R298_inventory_recorded_revision':inv.get('R294_recorded_source_revision'),
  'R300_translation_revision_in_original_receipts':res.get('source_revision_recorded'),
  'R300_actual_campaign_head_at_dispatch':correction.get('actual_campaign_head_at_dispatch'),
  'stale_planned_revision':correction.get('stale_planned_revision_in_original_receipts'),
  'correction_receipt_sha256':sha(r300/'revision-correction.json'),
  'note':'The R300 launch/result receipts retain the stale planned revision; this separate correction records the actual campaign HEAD at dispatch. The unrelated preexisting R241 promotion receipt is excluded and not used as R300 evidence.'},
 'stages':[
  {'stage':'R298 read-only slice.last closure inventory','input_sha256':inv.get('input_llbc_sha256'),'output_sha256':sha(r298/'inventory.json'),'recorded_source_revision':inv.get('R294_recorded_source_revision'),'exit_status':'N/A: metadata inventory only','status':'inventory completed; Fun12 → Type9 typed closure; no translation/build','details':{'root':inv.get('root'),'closure':inv.get('closure'),'has_errors':inv.get('has_errors'),'pinned_reorder_sha256':inv.get('pinned_reorder_rules_sha256')},'print_axioms':'NOT APPLICABLE: no Lean compilation'},
  {'stage':'R299 metadata-only Slice.last projection','input_sha256':audit.get('input_sha256'),'output_sha256':audit.get('output_sha256'),'recorded_source_revision':inv.get('R294_recorded_source_revision'),'exit_status':'N/A: local deterministic metadata projection','status':'projection audit passed; retained Type9 and Fun12 rows in original array positions','details':{'roots':audit.get('roots'),'ordered_decls':audit.get('ordered_decls'),'retained_rows':audit.get('retained_rows'),'typed_ast_closure_complete':True,'prepass_dependency_projection':'incomplete: removed implicit slice_len_fn dependency described by lead'},'print_axioms':'NOT APPLICABLE: no Lean compilation'},
  {'stage':'R300 exact projected-input translation attempt','input_sha256':res.get('source_sha256'),'output_sha256':None,'recorded_source_revision':res.get('source_revision_recorded'),'binary_sha256':res.get('binary_sha256'),'exit_status':res.get('translator_exit_status'),'wall_seconds':res.get('resource_metrics',{}).get('gnu_time_wall_seconds'),'peak_rss_kib':res.get('resource_metrics',{}).get('gnu_time_peak_rss_kib'),'swap_count':res.get('resource_metrics',{}).get('gnu_time_swaps'),'resource_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'status':'FAILED before generated output: Inconsistent projection for Generated_Expressions.PtrMetadata','details':{'translator_failure':res.get('observed_failure'),'generated_output_exists':res.get('root_emission',{}).get('generated_dir_exists'),'translation_manifest_exists':res.get('root_emission',{}).get('translation_json_exists'),'template_holes':'unchecked because no generated output','source_revision_discrepancy':{'recorded':res.get('source_revision_recorded'),'actual_current':'04d7d1b635ddb7c9af2ee3e2df3cdb68ae68bb43'},'command':cmd.get('command')},'print_axioms':'NOT APPLICABLE: no Lean compilation'}
 ],
 'R300_revision_correction_receipt':{'file':'artifacts/r300-slice-last-translation/revision-correction.json','sha256':sha(r300/'revision-correction.json'),'actual_campaign_head_at_dispatch':correction.get('actual_campaign_head_at_dispatch'),'scope_note':correction.get('scope')},
 'boundary':'R289 existing direct metadata lowering depends on unique slice_len_fn declaration; the R299 projection omitted this implicit prepass dependency despite typed AST closure completeness. Classify as incomplete tool-prepass dependency projection, not semantic AST modification or proof. R300 failure is preserved. No source semantics, proof, privacy/security, or release gate is established.',
 'omissions':[], 'archived_file_count':len(files),'archived_bytes':sum(x['size_bytes'] for x in files),'files':files
}
(A/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
lines=[]
for p in sorted(A.rglob('*')):
 if p.is_file() and p.name!='SHA256SUMS': lines.append(f'{sha(p)}  {p.relative_to(A)}')
(A/'SHA256SUMS').write_text('\n'.join(lines)+'\n')
print(json.dumps({'files':len(files),'bytes':sum(x['size_bytes'] for x in files),'checksums':len(lines),'manifest_sha256':sha(A/'manifest.json')},indent=2))
