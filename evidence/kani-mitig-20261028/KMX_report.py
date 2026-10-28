from pathlib import Path
import json,re,subprocess
E=Path(__file__).resolve().parent
result_summary=subprocess.run(['python3',str(E/'KMX_results.py')],capture_output=True,text=True,check=True)
(E/'KMX_results_summary.txt').write_text(result_summary.stdout)
results=json.loads((E/'KMX_RESULTS.json').read_text())
configs=json.loads((E/'KMX_TRIGGER_CONFIGS.json').read_text())
plan=json.loads((E/'KMX_ALL_REPLAY_PLAN.json').read_text())
ex=json.loads((E.parent/'kani-diag-20261027/KDX_EXPOSURE.json').read_text())
lines=['# KMX copy mitigation finding','', 'Frozen release revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Pinned cargo-kani 0.67.0 / CBMC 6.8.0. Scratch-only work; no release-source changes or toolchain adoption.','', '## Configuration map','', 'Each row has independent expected-value and wrong-zero controls. Native R002 checks all 49 original shapes and the loop replacements. R003 checks the three additional slice-parameter/literal shapes; R005 adds native value controls for 1, 255 and 256. These are concrete last-element observations, not a universal characterization of all inputs or compiler lowering. Source lengths are symbolic but constrained to the listed size, except slice_constant rows which use literal full-array copies; destinations start zeroed. A short copy uses a matching destination subslice of a larger backing allocation.','', '| ID | Type | Bytes | API / destination | Offset / extra | Expected / wrong | Interpretation |','|---|---|---:|---|---|---|---|']
matrix=[]
for c in configs:
 pair=[]
 for kind in ['correct','wrong']:
  hits=[r for r in results if re.search(r'(?:pending_|bounded_|values_)?'+c['id']+'_'+kind+r'$',r['harness'])]
  pair.append(hits[-1] if hits else None)
 a,b=pair
 label='NOT RUN' if not a or not b else 'TIMEOUT' if any(r['result']=='TIMEOUT' for r in pair) else 'INCONCLUSIVE (unwind)' if any(r['unwind_failure'] for r in pair) else 'DISAGREES' if a['result']=='FAIL' and b['result']=='PASS' else 'agrees on fixture' if a['result']=='PASS' and b['result']=='FAIL' else 'INCONCLUSIVE'
 status=' / '.join((r['result']+(' (unwind)' if r['unwind_failure'] else '')+' '+r['attempt'].replace('KMX_','')) if r else 'NOT RUN' for r in pair)
 lines.append(f"| {c['id']} | `{c['ty']}` | {c['width']*c['n']} | {c['op']} / {c['dest']} | {c['offset']} / {c['extra']} | {status} | {label} |")
 matrix.append(dict(config=c,expected=a,negative=b,interpretation=label))
lines+=['', 'Across the 55 tested configurations: '+', '.join(str(sum(x['interpretation']==kind for x in matrix))+' '+kind for kind in ['DISAGREES','agrees on fixture','TIMEOUT','NOT RUN'])+'. The symbolic-length array/slice u32 fixtures also disagree at values 1, 255 and 256 (R005 native controls), so this is not specific to 512. Direct full-array literal copies of one and sixteen u32 elements agree (K037/K038). The source/lowering distinction is observed, not an established internal cause.', '']
lines+=['','The observed disagreement includes one u32 (4 bytes), so it is not restricted to the original 64-byte fixture. Flat byte copies and the tested Vec variants must not be generalized to untested shapes. For nested arrays, the original bounds counted outer elements and underbounded equality loops. K030–K035 change those source bounds to 35, covering the 32-byte equality loop, and retain the original failed drafts. Only completed adequately bounded pairs receive a classification. Larger typed-copy timeouts remain inconclusive. Internal model root cause remains open.','','## Validated replacements','', 'Six explicit element-loop replacements are packaged in [KMX_copy_stubs.patch](KMX_copy_stubs.patch); [KMX_STUB_USAGE.md](KMX_STUB_USAGE.md) gives attributes, preconditions and scope. K008: all six expected controls PASS; all six negative controls FAIL; no unwinding failure. R002: optimized native differential, 1,466,538 checks across exhaustive small inputs and seeded larger inputs, all five types and 49 matrix shapes. L003: `lean/KMX_CopyMeaning.lean` compiles; indexed copy, frame, append and retained-prefix laws have only accepted axioms. This is a value-level specification, not a proved Rust-to-Lean refinement.','','## Exposure replay','', 'Only rows with a reached copy require mitigation replay. Other audit rows are retained as EXCLUDED with their original reason. Passing rows confirm only the original selected property under its original auxiliary stubs and assumptions; they do not establish an entire release function or bridge.','', '| Original | Harness | Result / attempt |','|---|---|---|']
reruns=[]
for row in ex:
 p=next((p for p in plan if p['original']==row['id']),None)
 if not p:status='EXCLUDED';reason=row['verdict'];attempt=''
 else:
  hits=[r for r in results if r['harness']==p['harness']]
  r=hits[-1] if hits else None
  status=r['result'] if r else 'NOT RUN';attempt=r['attempt'] if r else '';reason='unwinding failure' if r and r['unwind_failure'] else ''
 lines.append(f"| {row['id']} | `{row['harness']}` | {status} {attempt} {reason} |")
 reruns.append(dict(id=row['id'],harness=row['harness'],status=status,attempt=attempt,reason=reason))
lines+=['','## Newest release comparison','']
latest=E/'KMX_LATEST_RESULT.md'
lines+=[latest.read_text() if latest.exists() else 'Installation and reproducer pending. Latest published release lookup: [Kani 0.68.0](https://github.com/model-checking/kani/releases/tag/kani-0.68.0). No upgrade adopted.']
lines+=['','## Execution and limitations','', 'K004 was our omitted-input launcher error: `KMX_native.rs` was uploaded after admission KMX_UPLOAD4. K005 continued successfully; K004 remains a failed pre-Kani attempt, not a verification result. K001/K003/K007 were failed setup drafts. K010 failed on missing harness imports/helpers. K011 exposed additional unused historical contract attributes and incomplete auxiliary stub snapshots; scratch overlays were corrected without changing any selected property. L001/L002 were failed Lean drafts. Receipts, source snapshots, graph validation and exact commands are retained per attempt.','']
counts={k:len(list(E.glob(f'KMX_{prefix}[0-9][0-9][0-9].json'))) for k,prefix in [('Kani','K'),('Lean','L'),('Rust','R')]}
lines += [f"Conservative configured attempts: Kani {counts['Kani']}/80; Lean {counts['Lean']}/30; Rust {counts['Rust']}/15. Each admitted build uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, one scope at a time. Cargo graph is validated against the copied frozen lock offline before each gate; before/after hashes are recorded. Optimized Rust profile. Persistent cache retained; no keys touched; no push.", '', '**Confirmed earlier properties:** '+(', '.join(r['id'] for r in reruns if r['status']=='PASS') or 'none yet')+'. No complete release-function confirmation is claimed beyond the selected passing properties.']
summary={status:sum(r['status']==status for r in reruns) for status in ['PASS','FAIL','TIMEOUT','NOT RUN','EXCLUDED']}
lines[4:4]=['', 'Summary: the one-u32 fixture exhibits a false-PASS on the pinned model. Six loop replacements have paired Kani controls, native differential checks and Lean value laws. Exposure replay outcomes: '+', '.join(str(n)+' '+k for k,n in summary.items())+'. TIMEOUT does not restore earlier proof credit.', '']
groups={
 'compact::expand_values':['LPa_K004','LPl_K015','LPn_K001','LPg_K011','LPg_K012','LPh_K018','LPh_K019','LPh_K020','LPh_K021'],
 'r1_wire::ValidatedRecord::decode_k':['LPn_K010'],
 'verifier::checkpoint / append stages':['LPm_K001','LPm_K003','LPm_K004','LPm_K005','LPe_K015','LPe_K016','LPe_K017','LPe_K018','LPe_K019','LPf_K027','LPi_K012','LPi_K013','LPi_K017','LPi_K018'],
 'QM31::write_le_bytes (existing CM31 byte stub retained)':['LPi_K005','LPi_K006','LPi_K007','LPi_K008','LPi_K009','LPi_K010'],
 'candidate::wide_view':['LPa_K015'],
 'prepared_claim serializer stages':['LPb_K016','LPe_K005'],
 'ASF8 stores helper (original local gate, not full release serializer)':['NBH_K029']}
lines+=['', '## Earlier results confirmed, by target', '', '| Target | Confirmed earlier property IDs | Remaining selected properties |','|---|---|---|']
for target,ids in groups.items():
 selected=[r for r in reruns if r['id'] in ids]
 passed=', '.join(r['id'] for r in selected if r['status']=='PASS') or 'none'
 remaining=', '.join(r['id']+' '+r['status'] for r in selected if r['status']!='PASS') or 'none'
 lines.append('| '+target+' | '+passed+' | '+remaining+' |')
lines+=['', 'These confirmations restore only the named harness results under their retained assumptions. No complete P6 leaf, composed bridge or release-function theorem is promoted by this packet. No exposure replay has produced a concrete property counterexample if the FAIL count above is zero; TIMEOUT supplies no counterexample to replay natively. Native wrong-zero refutations for diagnostic fixtures are R002/R003/R005.', '']
lines+=['', 'The K006 outer timeout ended before its in-process after-lock check; this missing contemporaneous check is retained as a limitation. Subsequent graph checks found the pinned lock unchanged. No unchanged timeout was resubmitted. The nested-array retry changes a demonstrably inadequate source bound; no memory cap or timeout was raised. Detailed target, exit status, wall time, peak RSS/cgroup memory, swap, source revision/hashes and axioms are in `KMX_LEDGER.json` and the individual receipts.']
if (E/'KMX_CLEANUP.json').exists():
 cleanup=json.loads((E/'KMX_CLEANUP.json').read_text())
 lines+=['', '## Final audit', '', str(cleanup['source_files_checked'])+' frozen scratch source files were checked. Only '+str(len(cleanup['changed_scratch_parents']))+' intended scratch parent overlays differ; selected property bodies remain unchanged apart from namespace. No repository crates/programs were edited. All preexisting coherent/cache objects are unchanged. Own Cargo target, native binaries and solver scratch were removed; the persistent cache and installed scratch toolchain were retained. `KMX_CLEANUP.json` records exact hashes and removals. Final exposure table has no NOT RUN rows among the 34 reached-copy targets. No source counterexample was found; 16 TIMEOUT rows remain unconfirmed.']
(E/'KMX_FINDING.md').write_text('\n'.join(lines)+'\n')
(E/'KMX_CONFIGURATION_MAP.json').write_text(json.dumps(matrix,indent=2)+'\n')
(E/'KMX_RERUN_STATUS.json').write_text(json.dumps(reruns,indent=2)+'\n')
