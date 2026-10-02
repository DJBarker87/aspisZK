#!/usr/bin/env python3
"""Inventory the already-copied R280-R303 archival candidate; performs no builds."""
import hashlib, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
ARCH=pathlib.Path(__file__).resolve().parent
SRC=ROOT/'.r21-scratch'
REV='380c7d46c9719dcfcab601fac2607861d47dee02'
CAPS={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}

def load(base,name): return json.loads((base/name).read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def archived(name): return ARCH/'artifacts'/name

stages=[]
# Each row is saved-run provenance. Metadata-only stages correctly leave execution metrics N/A.
def stage(name,target,input_sha,output_sha,source_rev,exit_code,wall,rss,swap,caps,status,details=None):
    stages.append({'stage':name,'target':target,'input_sha256':input_sha,'output_sha256':output_sha,
      'source_revision_recorded':source_rev,'exit_status':exit_code,'wall_time':wall,
      'peak_rss_kib':rss,'swap':swap,'resource_caps':caps,'status':status,
      'details':details or {},'print_axioms':'NOT APPLICABLE: no Lean compilation in this stage'})

r280=SRC/'r280-private-norm-batch-extract'; r280a=archived('r280-private-norm-batch-extract')
r280res=load(r280,'result.json'); r280acc=load(r280,'acceptance.json'); r280cmd=load(r280,'extract-command.json')
stage('R280 sourceful broad batch/try_norm diagnostic','R280PrivateNormBatch.llbc',None,r280res.get('llbc_sha256'),r280res.get('source_revision_recorded'),r280res.get('charon_exit_status'),r280acc.get('wall_time'),r280acc.get('peak_rss_kib'),r280acc.get('swaps'),load(r280,'launch.json').get('caps'),'REJECTED: has_errors=true despite Charons exit 0',{'has_errors':True,'accepted_as_proof_input':False,'roots':r280cmd.get('start_from'),'includes':r280cmd.get('include'),'README_was_prelaunch_and_is_retained_verbatim':True,'known_error':'Zip trait-clause/type mismatch; see extract.log and failure-inventory/'})

r282=SRC/'r282-private-norm-closures-extract'; r282res=load(r282,'rejected-result.json'); r282cmd=load(r282,'extract-command.json')
stage('R282 isolated try_norm closure extraction diagnostic','try_norm::_::call_once closure-pattern extraction (no LLBC emitted)',None,None,r282cmd.get('source_revision_recorded'),r282res.get('charon_exit_status'),r282res.get('wall_time'),r282res.get('peak_rss_kib'),r282res.get('swaps'),load(r282,'launch.json').get('caps'),'REJECTED: pinned driver returned 101; no LLBC',{'scope_exit_status':r282res.get('scope_exit_status'),'llbc_exists':False,'reason':r282res.get('reason'),'root':r282cmd.get('start_from')})

r283=SRC/'r283-private-norm-batch-extract'; r283res=load(r283,'result.json'); r283acc=load(r283,'acceptance.json'); r283cmd=load(r283,'extract-command.json')
r283hash=r283res['llbc_sha256']
stage('R283 original batch-only source extraction','R283PrivateNormBatch.llbc',None,r283hash,r283res.get('source_revision_recorded'),r283res.get('charon_exit_status'),r283acc.get('wall_time'),r283acc.get('peak_rss_kib'),r283acc.get('swaps'),load(r283,'launch.json').get('caps'),'VALID SOURCE EXTRACTION: has_errors=false; metadata review only',{'has_errors':r283acc.get('has_errors'),'root':r283acc.get('root_name'),'root_id':r283acc.get('root_id'),'start_from':r283cmd.get('start_from'),'source_hashes':r283res.get('source_hashes'),'rustflags_sha256':r283cmd.get('rustflags_sha256')})

r288=SRC/'r288-private-batch-ordering'; r288audit=load(r288,'audit.json'); r288diag=load(r288,'failure-diagnostic.json')
stage('R288 manual root-Fun0 subset-order diagnostic','metadata ordering for Fun0; no ordered LLBC output',r288diag.get('input_sha256'),None,None,None,None,None,None,None,'FAILED CLOSED: TraitImpl 11 self-edge',{'diagnostic_sha256':sha(r288/'failure-diagnostic.json'),'audit_sha256':sha(r288/'audit.json'),'self_edge':r288diag.get('cycle_nodes'),'cycles_or_missing':True,'input_source_revision':r283res.get('source_revision_recorded'),'pinned_reorder_sha256':r288diag.get('pinned_reorder_sha256'),'attempted_process_metrics':'not recorded; local metadata diagnostic'})

r290=SRC/'r290-private-batch-ordering'; r290audit=load(r290,'audit.json'); r290diag=load(r290,'failure-diagnostic.json')
stage('R290 limited recursive TraitImpl subset-order diagnostic','metadata ordering for Fun0; no ordered LLBC output',r290diag.get('input_sha256'),None,None,None,None,None,None,None,'FAILED CLOSED: TraitImpl 2 self-edge',{'diagnostic_sha256':sha(r290/'failure-diagnostic.json'),'audit_sha256':sha(r290/'audit.json'),'self_edge':r290diag.get('next_fail_closed_cycle'),'input_source_revision':r283res.get('source_revision_recorded'),'pinned_reorder_sha256':r290diag.get('pinned_reorder_sha256'),'attempted_process_metrics':'not recorded; local metadata diagnostic'})

r292o=SRC/'r292-original-r283-order-audit'; r292oa=load(r292o,'audit.json')
stage('R292 audit of original Charon ordered_decls','R283 original translated.ordered_decls and dependency IDs',r292oa.get('input_sha256'),sha(r292o/'audit.json'),None,None,None,None,None,None,'STRUCTURAL ORDER AUDIT: original Charon ordering resolves',{'input_source_revision':r283res.get('source_revision_recorded'),'has_errors':r292oa.get('has_errors'),'ordered_decls_groups':r292oa.get('ordered_decls_count'),'listed_ids':r292oa.get('listed_declarations'),'root_fun0':r292oa.get('root_fun0'),'manual_R288_R290_attempts_distinct_and_unneeded':r292oa.get('manual_subset_order_diagnostics_are_distinct_and_unneeded_for_original_order'),'execution_metrics':'not recorded; metadata-only audit'})

r292=SRC/'r292-private-batch-translation'; r292tr=load(r292,'translation-result.json'); r292res=load(r292,'result.json'); r292cmd=load(r292,'translate-command.json')
stage('R292 translation of exact original R283 LLBC','AspisR292PrivateBatch.circle_norm.joined_inverse.line_norm.r110_norm.batch',r292tr.get('source_sha256'),r292tr.get('generated_sha256',{}).get('generated/AspisR292PrivateBatch/Funs.lean'),r292tr.get('source_revision_recorded'),r292tr.get('translator_exit_status'),r292tr.get('resource_metrics',{}).get('wall_time'),r292tr.get('resource_metrics',{}).get('peak_rss_kib'),r292tr.get('resource_metrics',{}).get('swaps'),load(r292,'launch.json').get('caps'),'TRANSLATION EXIT 0: batch definition emitted; external templates unresolved',{'input_has_errors':False,'input_source_sha256':r283hash,'binary_sha256':r292tr.get('binary_sha256'),'root_emission':r292tr.get('root_emission'),'unresolved_external_template_declarations':r292tr.get('unresolved_external_template_declarations'),'initial_false_negative_preserved':(r292/'translation-result.initial-root-scan.json').exists()})

r293=SRC/'r293-private-norm-batch-extract'; r293res=load(r293,'result.json'); r293acc=load(r293,'acceptance.json'); r293cmd=load(r293,'extract-command.json')
stage('R293 broad selected iterator sourceful extraction','R293PrivateNormBatch.llbc',r293res.get('input_sha256',r283hash),r293res.get('llbc_sha256'),r293res.get('source_revision_recorded'),r293res.get('charon_exit_status'),r293acc.get('wall_time'),r293acc.get('peak_rss_kib'),r293acc.get('swaps'),load(r293,'launch.json').get('caps'),'REJECTED: has_errors=true, unsupported SliceIter::next_chunk union constant',{'has_errors':r293res.get('has_errors'),'accepted_as_proof_input':r293acc.get('accepted_as_proof_input'),'source_hashes':r293res.get('source_hashes'),'start_from':r293cmd.get('start_from'),'includes':r293cmd.get('include'),'error_details':'postflight.json / result.json'})

r294=SRC/'r294-private-norm-batch-extract'; r294res=load(r294,'result.json'); r294audit=load(r294,'target-body-audit.json'); r294cmd=load(r294,'extract-command.json')
r294log=(r294/'extract.log').read_text()
r294wall=__import__('re').search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',r294log).group(1).strip()
r294rss=int(__import__('re').search(r'Maximum resident set size \(kbytes\): (\d+)',r294log).group(1))
r294swap=int(__import__('re').search(r'Swaps: (\d+)',r294log).group(1))
stage('R294 narrow selected Chain and iterator bodies extraction','R294PrivateNormBatch.llbc',r294res.get('input_sha256',r283hash),r294res.get('llbc_sha256'),r294res.get('source_revision_recorded'),r294res.get('charon_exit_status'),r294wall,r294rss,r294swap,load(r294,'launch.json').get('caps'),'VALID EXTRACTION: has_errors=false; no translation/proof',{'has_errors':r294res.get('has_errors'),'root_fun0':r294res.get('root_fun0'),'selected_body_census':r294res.get('selected_body_census'),'generic_iterator_try_fold':'Fun58 remains Foreign/Opaque','command_start_from':r294cmd.get('start_from'),'includes':r294cmd.get('include'),'target_body_audit_sha256':sha(r294/'target-body-audit.json')})

r295=SRC/'r295-private-batch-translation'; r295res=load(r295,'result.json'); r295tr=load(r295,'translation-result.json'); r295cmd=load(r295,'translate-command.json')
stage('R295 translation attempt of exact R294 LLBC with original Aeneas binary','AspisR295PrivateBatch batch root; no Lean output emitted',r295res.get('source_sha256'),None,r295res.get('source_revision_recorded'),r295res.get('translator_exit_status'),r295res.get('resource_metrics',{}).get('gnu_time_wall_seconds'),r295res.get('resource_metrics',{}).get('gnu_time_peak_rss_kib'),r295res.get('resource_metrics',{}).get('gnu_time_swaps'),load(r295,'launch.json').get('caps'),'REJECTED: associated-type-constraint signature sanity check; no output',{'input_has_errors':False,'input_sha256':r295res.get('source_sha256'),'binary_sha256':r295res.get('binary_sha256'),'generated_output_exists':r295tr.get('generated_dir_exists'),'diagnostic':r295res.get('observed_failure'),'translation_result':r295tr})

# R296 is a read-only pinned-source preflight; R297/R303 are saved campaign outputs.
r296=SRC/'r296-monomorphization-preflight'; r296i=load(r296,'inspection.json')
stage('R296 pinned Charon monomorphization option source inspection','read-only option/preset source inventory; no build or translation',None,None,r296i.get('commit'),None,None,None,None,None,'READ-ONLY SOURCE INSPECTION',{'repository':r296i.get('repository'),'method':r296i.get('method'),'facts_from_source':r296i.get('facts_from_source'),'scope_limit':r296i.get('scope_limit'),'source_hashes':load(r296,'source-hashes.json').get('source_files')})

r297=SRC/'r297-private-norm-batch-monomorphized'; r297res=load(r297,'result.json'); r297acc=None
r297log=(r297/'extract.log').read_text()
r297wall=__import__('re').search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',r297log).group(1).strip()
r297rss=int(__import__('re').search(r'Maximum resident set size \(kbytes\): (\d+)',r297log).group(1))
r297swap=int(__import__('re').search(r'Swaps: (\d+)',r297log).group(1))
r297_input_sha=load(SRC/'r294-private-norm-batch-extract','result.json').get('llbc_sha256')
stage('R297 monomorphized sourceful private norm batch extraction','R297PrivateNormBatch.llbc',r297_input_sha,r297res.get('llbc_sha256'),r297res.get('source_revision_recorded'),r297res.get('charon_exit_status'),r297wall,r297rss,r297swap,load(r297,'launch.json').get('caps'),'VALID SOURCE EXTRACTION: has_errors=false; metadata-valid monomorphized graph',{'has_errors':r297res.get('has_errors'),'input_sha256':r297_input_sha,'root_fun0':r297res.get('root_fun0'),'selected_body_census':r297res.get('selected_body_census'),'source_hashes':r297res.get('source_hashes'),'monomorphize':True,'chain_try_fold':'reachable transparent body; no residual binder type constraints','remaining_opaque_frontier':['Iterator::try_fold Fun36','Iterator::try_fold Fun38','ControlFlow::branch Fun37','ControlFlow::from_output Fun39','ControlFlow::from_residual Fun40']})

r303=SRC/'r303-private-batch-translation'; r303res=load(r303,'result.json'); r303tr=load(r303,'translation-result.json')
stage('R303 translation of exact R297 monomorphized batch with original Aeneas binary','AspisR303PrivateBatch batch root; no Lean output emitted',r303res.get('source_sha256'),None,r303res.get('source_revision_recorded'),r303res.get('translator_exit_status'),r303res.get('resource_metrics',{}).get('gnu_time_wall_seconds'),r303res.get('resource_metrics',{}).get('gnu_time_peak_rss_kib'),r303res.get('resource_metrics',{}).get('gnu_time_swaps'),load(r303,'launch.json').get('caps'),'REJECTED: unexpected erased region; translation stopped before Lean output',{'input_has_errors':False,'input_sha256':r303res.get('source_sha256'),'binary_sha256':r303res.get('binary_sha256'),'generated_output_exists':r303tr.get('generated_dir_exists'),'failure':r303res.get('observed_failure'),'opaque_reachable_helpers':r303res.get('input_opaque_reachable_helpers'),'systemd_runtime_ms':r303res.get('resource_metrics',{}).get('systemd_service_runtime_ms'),'scope_swap_peak_bytes':r303res.get('resource_metrics',{}).get('systemd_scope_swap_peak_bytes')})

# Auxiliary read-only signature failure inventory, copied in full.
faildir=SRC/'r295-signature-failure-inventory'
failinfo={'available':True,'directory':'artifacts/r295-signature-failure-inventory','source_revision_recorded':'380c7d46c9719dcfcab601fac2607861d47dee02 (R295 translation campaign; standalone excerpt inventory does not record a separate revision)','files':{},'scope':'Pinned Aeneas SymbolicToPureTypes signature constraint check and Rust Iterator::try_fold source excerpt; diagnostic only.'}
for p in sorted(faildir.rglob('*')):
    if p.is_file(): failinfo['files'][str(p.relative_to(faildir))]={'size_bytes':p.stat().st_size,'sha256':sha(p)}

# R280 omitted large decoded artifact metadata and reproducibility.
rd=(SRC/'r280-private-norm-batch-extract'/'decoded.json')
omit={'original_relative_path':'.r21-scratch/r280-private-norm-batch-extract/decoded.json','omitted_from_candidate':True,'size_bytes':rd.stat().st_size,'sha256':sha(rd),'reconstruction':'HashCons expansion over retained R280PrivateNormBatch.llbc using tools/expand_r280_hashcons.py. Verified once: 673 table entries; 0 cycles; 0 missing IDs; regenerated byte count and SHA match exactly. Reconstructed output was temporary and removed.','expected_regenerated_size_bytes':34987246,'expected_regenerated_sha256':'e28ef3384b2e2345a2e95ff431d7096ef9eb9cf577ffd3c0852848701b6f86e1'}

# Archived file inventory; only decoded.json is intentionally absent from its source stage.
file_inventory=[]
for p in sorted((ARCH/'artifacts').rglob('*')):
    rel=p.relative_to(ARCH)
    if p.is_file():
        source_rel=None
        if rel.parts[1] in [
          'r280-private-norm-batch-extract','r282-private-norm-closures-extract','r283-private-norm-batch-extract','r288-private-batch-ordering','r290-private-batch-ordering','r292-original-r283-order-audit','r292-private-batch-translation','r293-private-norm-batch-extract','r294-private-norm-batch-extract','r295-private-batch-translation','r295-signature-failure-inventory','r296-monomorphization-preflight','r297-private-norm-batch-monomorphized','r303-private-batch-translation']:
          source_rel='.r21-scratch/'+str(pathlib.Path(*rel.parts[1:]))
        if rel.parts[-2:] == ('inputs','R283PrivateNormBatch.llbc'):
          source_rel='.r21-scratch/r283-private-norm-batch-extract/R283PrivateNormBatch.llbc'
        if rel.parts[-2:] == ('inputs','R297PrivateNormBatch.llbc'):
          source_rel='.r21-scratch/r297-private-norm-batch-monomorphized/R297PrivateNormBatch.llbc'
        file_inventory.append({'path':str(rel),'size_bytes':p.stat().st_size,'sha256':sha(p),'original_source_path':source_rel})

manifest={'candidate':'R303 batch library frontier; archival candidate prepared for lead review, not published/staged/committed.',
 'source_revision_context':{'latest_source_context_revision':'b87e6b73671c5bf747de1b0bf3dd324fc428912c','campaign_revision':'380c7d46c9719dcfcab601fac2607861d47dee02','R280_launch_preparation_revision':'e8601f2d13149484f3a6a0304cd48892821363c4','frozen_source_root':'/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a','frozen_source_root_git_metadata':'none; individual Rust/Cargo source hashes are preserved in extraction receipts'},
 'stages':stages,'failure_inventory':failinfo,'omissions':[omit],
 'archived_file_count':len(file_inventory),'archived_bytes':sum(f['size_bytes'] for f in file_inventory),'files':file_inventory,
 'interpretive_boundary':'R283 is valid source extraction; R283 original ordered_decls is structurally usable. R292 emits an actual batch Lean body but has five function and one type external template obligations. R293 has_errors=true. R294 has_errors=false and includes specialized any/try_fold bodies; generic Iterator::try_fold remains opaque. R295 binary rejects associated-type-constraint signatures before emission. R297 monomorphization yields a metadata-valid source graph: reachable Chain::try_fold has no binder type constraints, while instantiated Iterator::try_fold and ControlFlow calls remain Foreign/Opaque. R303 uses the exact R297 LLBC and original binary, then stops at Unexpected erased region in SymbolicToPureTypes.ml:848 / iterator.rs:2486–2490; no Lean output. All batch/source execution/privacy/security theorems remain unproved. No generic semantic replacement is claimed.'}
(ARCH/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
# SHA256SUMS covers all archive files except itself; manifest includes every copied input and its hash.
lines=[]
for p in sorted(ARCH.rglob('*')):
    if p.is_file() and p.name!='SHA256SUMS': lines.append(f'{sha(p)}  {p.relative_to(ARCH)}')
(ARCH/'SHA256SUMS').write_text('\n'.join(lines)+'\n')
print(json.dumps({'stages':len(stages),'files':len(file_inventory),'bytes':sum(f['size_bytes'] for f in file_inventory),'manifest_sha256':sha(ARCH/'manifest.json'),'checksums_entries':len(lines)},indent=2))
