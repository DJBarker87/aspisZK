#!/usr/bin/env python3
"""Read-only R426 evidence integrity and precisely scoped diagnostic verification."""
import copy, hashlib, json, pathlib, sys
R=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'bundle-manifest.json').read_text())
errors=[rel for rel,h in m['files'].items() if not (R/rel).is_file() or sha(R/rel)!=h]
actual={p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_file()}
errors.extend(sorted(actual-set(m['files'])-{'bundle-manifest.json'}))
errors.extend(str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and p.suffix in {'.exe','.o','.a','.so','.pyc','.olean','.cmo','.cmx'})
a=json.loads((R/'provenance/R396PrivateBatchUnmonomorphized.llbc').read_text())
b=json.loads((R/'mir-diagnostic-plan/R426OriginalUllbc.llbc').read_text())
raw=json.loads((R/'mir-diagnostic-plan/result.json').read_text())
audit=json.loads((R/'lead-audit/native-map-comparison/raw-comparison-and-map-audit.json').read_text())
receipt=json.loads((R/'lead-audit/diagnostic-metrics-receipt.json').read_text())
key=lambda v:json.dumps(v,sort_keys=True,separators=(',',':'))
rows=[x['translated']['short_names'] for x in (a,b)]
maps=[{key(x['key']):x['value'] for x in xs} for xs in rows]
c=copy.deepcopy(b)
optionchanges=[k for k in a['translated']['options'] if a['translated']['options'][k]!=b['translated']['options'][k]]
for k in ('dest_file','print_original_ullbc'):c['translated']['options'][k]=a['translated']['options'][k]
c['translated']['short_names']=a['translated']['short_names']
checks={
 'exact_pinned_old_input':sha(R/'provenance/R396PrivateBatchUnmonomorphized.llbc')=='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae',
 'exact_pinned_new_input':sha(R/'mir-diagnostic-plan/R426OriginalUllbc.llbc')=='ed43306eac05443a2f4f91121ba8e943a000a66b0d7273eabc40735c64c6f15d',
 'only_two_exact_option_changes':set(optionchanges)=={'dest_file','print_original_ullbc'} and a['translated']['options']['print_original_ullbc'] is False and b['translated']['options']['print_original_ullbc'] is True and a['translated']['options']['dest_file']=='/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc' and b['translated']['options']['dest_file']=='/home/dombarker/project-offloads/aspis-r426-original-ullbc-20261002-a/R426OriginalUllbc.llbc',
 'all_347_unique_map_entries_exact':all(len(xs)==len(mp)==347 for xs,mp in zip(rows,maps)) and maps[0]==maps[1],
 'all_other_fields_exact_including_list_order':c==a,
 'charon_success_initial_gate_failure_retained':raw['charon_exit_status']==0 and raw['baseline_comparison']['equal_after_operational_option_normalization'] is False and 'code=exited/status=1' in (R/'mir-diagnostic-plan/lead-launch.log').read_text(),
 'source_hashes_unchanged':raw['source_hashes_before']==raw['source_hashes_after'],
 'original_ullbc_exact_capture':sha(R/'mir-diagnostic-plan/original-ullbc.stdout')=='203ba64981a75e9348e96bdf2920f1905f42c6d756de3c644e60006a440ab412' and "_5 = TraitClause0::next<'4>(copy self)" in (R/'mir-diagnostic-plan/original-ullbc.stdout').read_text(),
 'lead_strict_native_map_audit_pass':audit['strict_comparison_result']['whole_decoded_llbc_equal_under_these_field_specific_normalizations'] is True and not audit['raw_diff_summary']['all_other_raw_leaf_differences'],
 'metrics_and_caps_recorded':receipt['wall_time_seconds']==14.45 and receipt['peak_rss_kib']==625372 and receipt['swap_count']==0 and receipt['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},
 'no_lean_claim':receipt['complete_axiom_report'].startswith('N/A') and not list(R.rglob('*.olean')),
}
report={'result':'PASS' if not errors and all(checks.values()) else 'FAIL','indexed_files':len(m['files']),'integrity_errors':errors,'checks':checks,'scope':'Saved diagnostic evidence only; no compiler run, Lean proof, source-preservation theorem or end-to-end security claim.'}
print(json.dumps(report,indent=2));sys.exit(0 if report['result']=='PASS' else 1)
