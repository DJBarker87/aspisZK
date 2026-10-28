from pathlib import Path
import json,re,subprocess
E=Path(__file__).resolve().parent
subprocess.run(['python3',str(E/'KMX_results.py')],stdout=subprocess.DEVNULL,check=True)
results=json.loads((E/'KMX_RESULTS.json').read_text())
configs=json.loads((E/'KMX_TRIGGER_CONFIGS.json').read_text())
plan=json.loads((E/'KMX_ALL_REPLAY_PLAN.json').read_text())
ex=json.loads((E.parent/'kani-diag-20261027/KDX_EXPOSURE.json').read_text())
lines=['# KMX copy mitigation finding','', 'Frozen release revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Pinned cargo-kani 0.67.0 / CBMC 6.8.0. Scratch-only work; no release-source changes or toolchain adoption.','', '## Configuration map','', 'Each row has independent expected-value and wrong-zero controls. Native R002 checks all 49 original shapes and the loop replacements. R003 separately checks the three additional slice-parameter/literal shapes when its terminal receipt is present. These are concrete last-element observations, not a universal characterization of all inputs or compiler lowering. Source lengths are symbolic but constrained to the listed size, except slice_constant rows which use literal full-array copies; destinations start zeroed. A short copy uses a matching destination subslice of a larger backing allocation.','', '| ID | Type | Bytes | API / destination | Offset / extra | Expected / wrong | Interpretation |','|---|---|---:|---|---|---|---|']
matrix=[]
for c in configs:
 pair=[]
 for kind in ['correct','wrong']:
  hits=[r for r in results if re.search(r'(?:pending_|bounded_)?'+c['id']+'_'+kind+r'$',r['harness'])]
  pair.append(hits[-1] if hits else None)
 a,b=pair
 label='NOT RUN' if not a or not b else 'TIMEOUT' if any(r['result']=='TIMEOUT' for r in pair) else 'INCONCLUSIVE (unwind)' if any(r['unwind_failure'] for r in pair) else 'DISAGREES' if a['result']=='FAIL' and b['result']=='PASS' else 'agrees on fixture' if a['result']=='PASS' and b['result']=='FAIL' else 'INCONCLUSIVE'
 status=' / '.join((r['result']+(' (unwind)' if r['unwind_failure'] else '')+' '+r['attempt'].replace('KMX_','')) if r else 'NOT RUN' for r in pair)
 lines.append(f"| {c['id']} | `{c['ty']}` | {c['width']*c['n']} | {c['op']} / {c['dest']} | {c['offset']} / {c['extra']} | {status} | {label} |")
 matrix.append(dict(config=c,expected=a,negative=b,interpretation=label))
lines+=['','The observed disagreement includes one u32 (4 bytes), so it is not restricted to the original 64-byte fixture. Flat byte copies and the tested Vec variants must not be generalized to untested shapes. For nested arrays, the original bounds counted outer elements and underbounded byte-level/equality loops; such failures do not establish a false-PASS. Larger typed-copy timeouts remain inconclusive. Internal model root cause remains open.','','## Validated replacements','', 'Six explicit element-loop replacements are packaged in [KMX_copy_stubs.patch](KMX_copy_stubs.patch); [KMX_STUB_USAGE.md](KMX_STUB_USAGE.md) gives attributes, preconditions and scope. K008: all six expected controls PASS; all six negative controls FAIL; no unwinding failure. R002: optimized native differential, 1,466,538 checks across exhaustive small inputs and seeded larger inputs, all five types and 49 matrix shapes. L003: `lean/KMX_CopyMeaning.lean` compiles; indexed copy, frame, append and retained-prefix laws have only accepted axioms. This is a value-level specification, not a proved Rust-to-Lean refinement.','','## Exposure replay','', 'Only rows with a reached copy require mitigation replay. Other audit rows are retained as EXCLUDED with their original reason. Passing rows confirm only the original selected property under its original auxiliary stubs and assumptions; they do not establish an entire release function or bridge.','', '| Original | Harness | Result / attempt |','|---|---|---|']
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
lines+=['', 'The K006 outer timeout ended before its in-process after-lock check; this missing contemporaneous check is retained as a limitation. Subsequent graph checks found the pinned lock unchanged. No unchanged timeout was resubmitted. Detailed target, exit status, wall time, peak RSS/cgroup memory, swap, source revision/hashes and axioms are in `KMX_LEDGER.json` and the individual receipts.']
(E/'KMX_FINDING.md').write_text('\n'.join(lines)+'\n')
(E/'KMX_CONFIGURATION_MAP.json').write_text(json.dumps(matrix,indent=2)+'\n')
(E/'KMX_RERUN_STATUS.json').write_text(json.dumps(reruns,indent=2)+'\n')
