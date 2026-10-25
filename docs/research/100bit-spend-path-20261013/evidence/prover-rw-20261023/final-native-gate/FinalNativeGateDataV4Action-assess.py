"""Finite local assessment of retained outputs; no process or remote execution."""
import ast,base64,hashlib,json,pathlib
E=pathlib.Path(__file__).resolve().parent;P='FinalNativeGateDataV4Action-'
T=pathlib.Path('tools/prover-rw-20261023/final-native-gate/prospective-data-v4')
def read(n):return json.loads((E/(P+n)).read_text())
def pin(p):
 b=p.read_bytes();return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def main():
 r=read('primary-stdout');primary=read('primary-receipt.json');exe=read('execution.json');status=read('status-receipt.json')
 props=dict(line.split('=',1) for line in (E/(P+'status.stdout')).read_text().splitlines())
 assert primary['exit']==exe['exit']==r['setup_exit']==78
 assert not primary['errors'] and status['exit']==0 and not status['errors']
 assert props==dict(ControlGroup='',LoadState='not-found',ActiveState='inactive',SubState='dead',ActiveEnterTimestampMonotonic='0',InvocationID='')
 t=ast.parse((T/'FinalNativeGate-data-transfer.py').read_text())
 rows=next(ast.literal_eval(n.value) for n in t.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='FILES' for x in n.targets))
 plan=json.loads(base64.b85decode(rows['FinalNativeGate-plan.json']['b85']))
 assert r['files']==46 and r['bytes']==525933 and r['root']==read('preflight.json')['transfer_root']
 report=dict(status='TRANSFER_REPORTED_SETUP_FAILED_TERMINAL_UNOBSERVED',main_new=1,conditional_new=1,primary=r,unit_status_properties=props,
  remote_closure='Named unit absent/inactive at sole status observation; no InvocationID or ControlGroup. Parent/child terminal content, cleanup and guard content unobserved; no universal process-tree closure claim.',
  actual_admission_and_controls='UNOBSERVED: prospective/inside/GO reports not returned; no reservation or limit PASS inferred from source or transfer success',
  source_assessment=dict(checkout_before='ce3fa578fe3b07caefe48a7417b590bf3cc1d3e1',execution_revision=exe['source_revision'],maintained_source='3e4b5df592',embedded_plan_source_revision=plan['source_revision'],embedded_plan_job_revision=plan['job_revision'],historical_evidence='unchanged, no newly attributed identity gate',fresh_local='receiver/transport/embedded bytes, manifest root, bootstrap and plan seals',reused='lead complete source/mocks/reproduction receipt pinned in preflight; not rerun',new_host='only exact transfer summary, fixed summary errors and sole unit status'),
  source_dependency_hashes={str(p):pin(p) for p in sorted(T.rglob('*')) if p.is_file()},
  metrics=dict(primary_transport={k:primary[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap')},local_wrapper={k:exe[k] for k in ('wall_seconds','peak_self_rss_bytes','peak_serial_child_rss_bytes','sampled_aggregate_peak_bytes','swap_self','swap_children')},conditional_status={k:status[k] for k in ('exit','wall_seconds','peak_self_rss_bytes','peak_child_rss_bytes','swap_self','swap_children')},remote_setup_metrics='UNOBSERVED'),
  missing_roles_from_frozen_plan_not_fresh_discoveries=plan['missing'],native_roots_proposed_not_validated=plan['native_roots'],host_runtime=plan['host_runtime'],native_runtime_dependencies=plan['native_runtime_dependencies'],cache_roots_selected=plan['cache_roots'],
  source_local_obstruction='Receiver rejects parent summary records before JSON decoding on regular/single-link/owner/mode&022 check. Exact violated subcondition not returned. _publish creates xb files with ambient umask and no explicit0600 mode; this is a possible source cause, not an observed host mode or the underlying setup failure.',
  local_mode_analysis=[dict(umask=oct(mask),creation_mode=oct(0o666 & ~mask),receiver_mode_accepts=not bool((0o666 & ~mask)&0o022)) for mask in (0,0o002,0o022,0o077)],
  next_deliverable='Lead review of the returned summary-visibility failure; separately authorize a minimal read-only metadata/terminal diagnostic or reviewed source-only summary publication repair with mocks. Existing fixed leaf now precludes unchanged receiver replay; no deletion/adoption/retry in this allocation.',
  assumptions_discharged='Only local reviewed byte identity and one returned transfer-root equality; no security or proof premise discharged',assumptions_retained='All SDK/std/runtime/allocator/extraction/sourceDrop/protocol/artifact/security joins, runtime/tool/loader/sysroot/cache/harness and actual admission/control identities',premise_changes='None; no theorem/source/protocol change',new_trust_assumptions='None',print_axioms='N/A DATA, no Lean invocation or theorem',both_deployed_targets='NOT ESTABLISHED',heavy_native_compiler_Lean_Kani_extraction_ELF_actual=0)
 with (E/(P+'assessment.json')).open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
 print(json.dumps(dict(status=report['status'],main_new=1,conditional_new=1,exit78_preserved=True)))
if __name__=='__main__':main()
