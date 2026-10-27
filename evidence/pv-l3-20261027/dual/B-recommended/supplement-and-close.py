from pathlib import Path
import json,re,time,hashlib,shutil,tomllib
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026');O=H/'dual-evidence/B-recommended';R=H/'dual-B-recommended';t=time.monotonic();cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
rec=json.loads((O/'receipt.json').read_text());pcs={}
for line in (O/'selected-disassembly.txt').read_text().splitlines():
 m=re.match(r'\s*([0-9a-f]+): (\S+)\s*(.*)',line)
 if m:pcs[m[1]]={'address':'0x'+m[1],'op':m[2],'args':m[3]}
rows=[]
def add(id,path,anchor,addresses,classification,ledger,obligation):
 lines=(R/path).read_text().splitlines();n=next(i for i,x in enumerate(lines) if anchor in x)
 rows.append(dict(id=id,source_revision=rec['source_revision'],path=path,line=n+1,source_context=lines[max(0,n-2):n+4],source_sha256=hashlib.sha256((R/path).read_bytes()).hexdigest(),instructions=[pcs[p] for p in addresses],classification=classification,ledger_rows=ledger,obligation=obligation))
add('R2','crates/aspis-prover/src/state_only_hiding.rs','fn m31(&mut self)',['138024','13803f','13804d','138104','138109','13814d','13824b','13835b'],'secret candidate rejection and history-dependent refill/cursor addresses',['V354','V373','V371'],'D268 rejection-count assessment retained; exact accepted-seed/rejected-prefix joint law remains P')
add('R3','crates/aspis-r1-cost-probe/src/host_semantic.rs','if !no_pole(compiled',['b5c5c','b5a1d'],'secret-dependent full pole verdict',['V360','V373'],'CT scan fixes N1 machine prefix issue; final verdict still charged to poleBad and native containment/joint simulation remains P')
add('R5','crates/aspis-prover/src/state_only_entropy.rs','fn m31(&mut self)',['13c834','13c84f','13c85d','13c914','13c918'],'private D expander rejection/refill/cursor addresses',['V353','V373','V371'],'same rejection-count assessment, independent expansion/caller joint law remains P')
add('R6','crates/aspis-r1-cost-probe/src/sampler.rs','pub fn gamma_sample',['cb544'],'raw Fiat-Shamir challenge carry branch',['V356','V373'],'public/challenge-dependent; complete rejected-prefix law still P')
add('R7','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs','pub fn two_outputs',['17d09c','17d0a5','17d0ae','17d0b9','17d0cf'],'commitment-domain canonicality and nonzero sentinel',['V373','V380-inversion'],'valid canonical/nonzero commitment boundary and native compiler association retained')
(O/'supplemental-findings.json').write_text(json.dumps({'binary_sha256':rec['binary_sha256'],'findings':rows},indent=2)+'\n')
# Correctly include the inlined ordered query scanner in coverage.
inv=json.loads((O/'inventory.json').read_text());extra=[r for r in inv if any(x in r['symbol'] for x in ['host_transcript::','host_work::','constraints_v4::sparse_eq_weights','CopyRecords::banks','M31::inv','QM31::try_inv'])]
(O/'extra-kernels.json').write_text(json.dumps({'scope':'public query/challenge provenance; fixed worker partition; challenge point pruning; compiler/inverse zero boundaries; not whole closure CT','ledger_rows':['V357','V358','V360','V370','V371','V373','V380-inversion'],'members':extra},indent=1)+'\n')
pins=json.loads((H/'B-recommended-source.json').read_text());bad=[p for p,v in pins['files'].items() if hashlib.sha256((R/p).read_bytes()).hexdigest()!=v['sha256']];assert not bad
oldpins=json.loads((H/'B-source.json').read_text());delta=[p for p,v in oldpins['files'].items() if pins['files'][p]['sha256']!=v['sha256']];assert delta==['tools/r1-cost-probe/Cargo.lock'],delta
old=tomllib.loads((H/'dual-B/tools/r1-cost-probe/Cargo.lock').read_text())['package'];new=tomllib.loads((R/'tools/r1-cost-probe/Cargo.lock').read_text())['package'];registry=lambda xs:{(v['name'],v['version'],v['source']):v for v in xs if 'source' in v};assert registry(old)==registry(new)
assert hashlib.sha256((H/'bin/devnet_spend-B-recommended').read_bytes()).hexdigest()==rec['binary_sha256']
assert hashlib.sha256((O/'full-disassembly.txt').read_bytes()).hexdigest()==json.loads((O/'extraction.json').read_text())['full_disassembly_sha256']
for name in ['findings.json','supplemental-findings.json']:
 for finding in json.loads((O/name).read_text())['findings']:
  for i in finding['instructions']:assert i==pcs[i['address'][2:]]
assert len([r for r in inv if r['symbol']=='aspis_r1_cost_probe::ct_pole::all_slots_clear'][0]['branches'])==3
assert not json.loads((O/'fixture-review.json').read_text())['linked_symbols']
# Preserve every scope's exact target/revision/native N/A axioms plus GNU-time metrics.
resources=[]
for folder,receipt,timelog in [(H/'recommended-lock','receipt.json','time.log'),(O,'receipt.json','time.log'),(O,'static-receipt.json','static-time.log'),(O,'review-receipt.json','review-time.log')]:
 x=json.loads((folder/receipt).read_text());ts=(folder/timelog).read_text();x['process_peak_RSS_KiB']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',ts)[1]);x['process_swaps']=int(re.search(r'Swaps: (\d+)',ts)[1]);resources.append(x)
(O/'resource-summary.json').write_text(json.dumps(resources,indent=2)+'\n')
# Explicit target-only cleanup; no account/key/recovery data is touched.
target=H/'recommended-target-B';existed=target.exists()
if existed:shutil.rmtree(target)
cleanup={str(p):p.exists() for p in [target,H/'target',H/'dual-target-A',R/'target']};assert not any(cleanup.values()),cleanup
(O/'cleanup.json').write_text(json.dumps({'removed_target':str(target),'target_previously_existed':existed,'target_exists_after':cleanup,'binary_retained':str(H/'bin/devnet_spend-B-recommended'),'no_key_or_wallet_touched':True},indent=2)+'\n')
result=dict(target='supplement reviewed findings, validate exact source/binary/lock/PC bindings and remove only Cargo targets',source_revision=rec['source_revision'],exit_status=0,wall_seconds=time.monotonic()-t,source_inputs=1303,source_mismatches=bad,candidate_delta=delta,registry_records_unchanged=len(registry(new)),limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']},cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),print_axioms='N/A (no Lean)',budget={'Lean':0,'Kani':0},whole_transitive_taint_audit_complete=False)
(O/'closure-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
