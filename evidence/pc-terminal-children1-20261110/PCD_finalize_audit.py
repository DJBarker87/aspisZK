from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
logs=lambda a:lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
roots=load('PCD_AUDIT_ROOTS.json')['groups'][0]
parse=lambda t:[json.loads(line[len('NEP_RESULT '):]) for line in t.splitlines() if line.startswith('NEP_RESULT ')]
results=parse(logs('PCD_L059'));fixtures=parse(logs('PCD_L058'))
allowed={'propext','Classical.choice','Quot.sound'}
assert len(results)==len(roots)==74
assert sorted(r['root'] for r in results)==sorted(roots)
assert all(r['equal'] and set(r['walked_axioms'])<=allowed and set(r['collect_axioms'])<=allowed for r in results)
assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
loaded=[json.loads(l) for l in lzma.decompress((E/'PCD_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(x['imports_match'] and not x['dangling'] for x in loaded)
assert 'PCD_SCAN_ZERO_DANGLING' in logs('PCD_L060')
binaries=[load('PCD_binary_'+mode+'.json') for mode in ['fixtures','proof0','scan']]
assert all(x['unchanged'] and x['exit']==0 and x['before']==x['after'] for x in binaries)
assert len({x['before'] for x in binaries})==1
attempts=[json.loads(l) for l in (E/'PCD_ATTEMPTS.jsonl').read_text().splitlines()]
counts={k:sum(x['attempt'].startswith('PCD_'+k) for x in attempts) for k in 'KLE'}
assert counts=={'K':80,'L':60,'E':12},counts
scope_fields=['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']
gate=[{k:r.get(k) for k in scope_fields} for r in attempts if r['attempt'] in ['PCD_L055','PCD_L056','PCD_L057','PCD_L058','PCD_L059','PCD_L060']]
assert all(r['exit_status']==0 for r in gate)
audit=dict(status='PASS',headline='AspisR1.RPx_Deployed.deployed',combined_import='PCD_COMBINED_IMPORT',includes=['NLS_COMBINED_IMPORT','NLO_COMBINED_IMPORT','NLF_SdkBorrowLaw'],new_current_modules=38,roots=len(results),allowed_axioms=sorted(allowed),all_raw_ax2_equal_standard=True,fixtures=fixtures,same_binary_sha256=binaries[0]['before'],loaded_modules=len(loaded),dangling_references=0,import_header_mismatches=0,NFX_scan_exit=0,gate_scopes=gate,budget_used=counts,budget_limits={'K':80,'L':60,'E':12},source_pin_manifest='PCD_CURRENT_SOURCE_CHECK.json',actual_import_hash_manifest='PCD_IMPORT_OBJECTS.json.xz',resource_policy='one scope at a time, MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax64; Lean-M7000; optimized Rust',trust='PCD_TRUST_RECLASSIFICATION.json',full_soundness_target_established=False)
(E/'PCD_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
row320=dict(row='POOL:320',function='next_pair_forest_lane_v1',status='CLOSED',method='CLOSED under (ah)/(ay)(3); PCD-RT-POOL320',root='PCD_Row320.result_state_effects',root_receipt='PCD_L051',model_composition='PCD_LaneBridge.result_state_effects',own_argument_domain='all typed Lane and complete TerminalResult arguments; only verified_afterstate read; no success/canonicality/capacity premise',native_positive=['PCD_K021','PCD_K025','PCD_K039','PCD_K041','PCD_K027'],native_controls=['PCD_K022','PCD_K026','PCD_K040','PCD_K042','PCD_K028'],source='b936275465600469312d1f058cdc91ea2a11f3dc:programs/aspis-pool/src/pair_forest.rs',source_coverage='PCD_SOURCE_COVERAGE.json',trust_reclassification='PCD-RT-POOL320; native contract semantic transport under existing P6/D188 option A; no new runtime assumption',gate='PCD_AUDIT.json')
values=load('PCD_NATIVE_VALUE_COVERAGE.json')
row314=dict(row='POOL:314',function='decode_terminal_request_box_v1',status='CLOSED',method='actual and reference extraction (av), source-ordered native segment composition (ay)(3)',root='PCD_RequestRoot.result_state_effects',projection_root='PCD_RequestRoot.emitted_reply',root_receipt='PCD_L053',reference_equality='PCD_RequestBridge.reference_eq_emitted',reference_receipt='PCD_L050',source_extraction=['PCD_E008','PCD_E009'],reference_extraction='PCD_E011',closed_callee='NLO request decoder packet at SAME arbitrary slice; PCD_SHARED_ROWS.json',own_argument_domain='all valid typed instruction_data slices, every length; full child Result and allocation-return/abort outcomes; no free child result/endpoint/zero-input premise',native_positive=values['positive_attempts']+['PCD_K058','PCD_K054'],native_controls=values['matched_controls']+['PCD_K047','PCD_K078','PCD_K055'],native_shape_controls=['PCD_K049','PCD_K050','PCD_K051','PCD_K052','PCD_K053','PCD_K060','PCD_K061','PCD_K062','PCD_K063','PCD_K064'],full_error_carrier='all 106 child constructors across seven error families; exact final InvalidInstructionData; full emitted ProgramError including String mapped, no ABI quotient',source='b936275465600469312d1f058cdc91ea2a11f3dc:programs/aspis-pool/src/pair_forest.rs',source_coverage='PCD_REQUEST_SOURCE_COVERAGE.json',retained_trust=['Allocator (existing named-in-contract item, aa)','P6/D188 native contract semantic transport, option-A reclassification'],excluded_native=['PCD_K043','PCD_K079','PCD_K080'],gate='PCD_AUDIT.json')
closed=dict(schema='PCD_STREAM_C_CLOSURES_V1',rows=[row314,row320],count=2,producer_hypotheses_discharged=[],full_soundness_target_established=False,artifact_pins='PCD_ARTIFACTS.json',caller_clauses='PCD_CALLER_CLAUSES.json')
(E/'PCD_CLOSED.json').write_text(json.dumps(closed,indent=1)+'\n')
assigned=[311,312,313,314,339,319,320,350,347,348]
delta=dict(owner='PCD_',stream='C',authority='NKZ POOL ids, NLO ledger23 combined gate',transitions=[{'row':'POOL:'+str(n),'from':'OPEN','to':'CLOSED' if n in [314,320] else 'OPEN','packet':'PCD_CLOSED.json' if n in [314,320] else None,'remaining':'PCD_REMAINING.md' if n not in [314,320] else None} for n in assigned],closed_count=2,open_count=8,PCB_rows={'POOL:344':'owned by PCB; target only, no instantiation','POOL:345':'owned by PCB; target only, no instantiation'},NIB_P1='OPEN',NIB_P2='OPEN:314 constituent closed;311/312/313/339 remain',NIB_P3='OPEN:320 constituent closed;319/315 remain',P4_330='out of scope',shared_verifier_rows_reowned=[],gate='PCD_AUDIT.json',full_soundness_target_established=False)
(E/'PCD_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
print('Audit verified: 74 standard-axiom roots, eight same-binary fixtures, 17069 coherent modules; proposed Stream C closures314/320, producer binders still OPEN.')
