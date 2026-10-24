#!/usr/bin/env python3
"""Audit normal-return source control; do not promote it to native totality."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-native-word-control-20261024';X=E/'s1-native-borrowed-helper-20261024'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for root in [P,X]:
 m=load(root/'manifest.json')
 for n,h in m['files'].items():
  p=root/n;assert p.resolve().is_relative_to(root.resolve()) and sha(p)==h
  assert p.suffix not in ['.olean','.llbc','.out','.exe','.o','.rlib','.bc','.so','.a']
wall=0.;peak=0;count=0;inventories=[]
for point in range(7):
 n=f's1-original-word-partition-point{point}-bounded-v1';A=P/'attempts'/n;r=load(A/'receipt.json');i=load(A/'input.json');cmd=r['command'];s=(A/'stdout.log').read_text()
 assert r['exit_status']==0 and r['swaps']==0 and 'VERIFICATION:- SUCCESSFUL' in s
 assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592'
 assert '--unwinding-assertions' in cmd and '--unwindset' in cmd and '--solver' in cmd and cmd[cmd.index('--solver')+1]=='cadical'
 assert '--partial-loops' not in cmd
 bounds=cmd[cmd.index('--unwindset')+1].split(',');assert len(bounds)==2
 assert all(int(x.rsplit(':',1)[1])==min(point+2,7) for x in bounds)
 assert all('Loop '+x.rsplit(':',1)[0]+':' in (P/f'loop-inventory-point{point}.log').read_text() for x in bounds)
 assert i['env']['RUSTFLAGS'].startswith('-C opt-level=3 -Z mir-opt-level=0')
 assert '-j' in cmd and cmd[cmd.index('-j')+1]=='1'
 inventories.append((i['tool_pins'],load(A/'all-local-before.json')['dependencies'],i['cargo_lock_sha256']))
 assert all(load(A/'all-local-after.json')['unchanged'].values())
 assert all(load(A/'dependency-postcheck.json')['unchanged'].values())
 src=P/'inputs/s1-claim-word-partition-v1-20261024'
 for rel,h in i['crate_source_pins'].items():assert sha(src/rel)==h
 checks=re.search(r'0 of (\d+) failed',s);assert checks;count+=int(checks[1]);wall+=r['wall_seconds'];peak=max(peak,r['peak_rss_kib'])
assert all(row==inventories[0] for row in inventories),'source/tool/lock drift across partition cases'
neg=P/'attempts/s1-word-last-value-negative-v1';nr=load(neg/'receipt.json');ns=(neg/'stdout.log').read_text();assert nr['exit_status']==1 and '1 of 906 failed' in ns and 'Failed Checks: assertion failed: eq8(words(value),VALUES[l])' in ns and 'timed out' not in ns
# Exact finite partition and source index/range proof, checked independently.
a=load(E/'accepted-targets.json')['targets']['S1FirstErrorPartitionV1'];lr=load(E/a['receipt']);assert lr['exit_status']==0
for report in lr['print_axioms']:
 x=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert x and set(re.findall(r'[A-Za-z_.]+',x[1]))<={'propext','Classical.choice','Quot.sound'}
# Source identity, not similarity of output fixtures.
def function(s,name):
 start=re.search(r'\bfn\s+'+re.escape(name)+r'\b',s).start();i=s.index('{',start);depth=0
 for j in range(i,len(s)):
  depth+=(s[j]=='{')-(s[j]=='}')
  if depth==0:return s[start:j+1]
 raise AssertionError(name)
compact=lambda s:re.sub(r'\s+','',s)
kit=(P/'inputs/s1-claim-word-partition-v1-20261024/src/lib.rs').read_text();ref=(X/'input/lib.rs').read_text()
for name in ['owned_scalar','owned_push','owned_sum','owned_claim_loops','prepared_claim_owned']:
 assert compact(function(kit,name))==compact(function(ref,name)),name
for revision in ['b2727acd3abf79315d18b754a260f58f4b1c6326','25866ec331cc7ce27dd9956609c11d32fa8fa58a','b797d6d360b460b527c046e37dad1106e8beeabc']:
 frozen=subprocess.check_output(['git','show',revision+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R,text=True)
 assert compact(function(kit,'prepared_claim'))==compact(function(frozen,'prepared_claim'))
# Borrowed private helper extraction is the SAME checked complete emission.
old=E/'s1-claim-owned-reference/borrowed-abi-extraction/generated/AspisS1OwnedNestedClaim';new=X/'baseline/generated/AspisS1OwnedNestedClaim'
clean=lambda s:compact(re.sub(r'/\-[\s\S]*?\-/','',s))
assert re.sub(r'/\-[\s\S]*?\-/','',(old/'Funs.lean').read_text())==re.sub(r'/\-[\s\S]*?\-/','',(new/'Funs.lean').read_text())
assert sha(old/'Types.lean')==sha(new/'Types.lean')
br=load(X/'baseline/attempt/receipt.json');bi=load(X/'baseline/input.json');assert br['exit_status']==0 and br['swaps']==0 and 'aeneas-b59d5188-lean432-extended-static' in bi['command'][0]
# Verify full-word predicates and the checked first-error partition actually
# used by the seven harnesses; no shortened carrier is installed.
s=(P/'inputs/s1-claim-word-partition-v1-20261024/src/proofs.rs').read_text()
for size,t in [(4,'u32'),(8,'u32'),(9,'u64')]:
 exact='fn eq%d(a:[%s;%d],b:[%s;%d])->bool{%s}'%(size,t,size,t,size,' & '.join('(a[%d]==b[%d])'%(j,j) for j in range(size)))
 assert exact in s
assert s.count('kani::assume(')==1 and 'kani::assume(ERROR_COLUMN<29)' in s
assert 'if p==ERROR_POINT && l==ERROR_COLUMN{Err(())}else{Ok(())}' in s
for text in ['assert_eq!(FIELD,if p==5{l+1}else{0})','assert_eq!(PUSH,145+index)','assert_eq!(FINISH,5)','assert_eq!(ADD,i)']:
 assert text in s,text
pins=load(E/'s1-native-word-control-source-pins.json')['files'];assert all(pins['crates/aspis-r1-cost-probe/src/'+n+'.rs']['all_equal'] for n in ['verifier','candidate'])
assert not pins['crates/aspis-r1-cost-probe/src/weights.rs']['all_equal'] and not pins['crates/aspis-r1-cost-probe/src/fast_pairing.rs']['all_equal']
formal_pins=load(E/'s1-first-error-partition-import-pins.json');accepted=load(E/'accepted-targets.json')['targets']
for module in ['S1FirstErrorPartitionV1','S1FirstErrorByteRangesV1']:
 row=accepted[module];receipt=load(E/row['receipt']);source=B/'lean-candidates/s126-caller-boundary-20261021'/(module+'.lean')
 assert receipt['exit_status']==0 and receipt['swaps']==0
 assert sha(source)==sha((E/row['receipt']).parent/'source.lean')==receipt['source_sha256']==formal_pins['targets'][module]['source_sha256']
 assert receipt['object_sha256']==formal_pins['targets'][module]['object_sha256']
 assert '-j1' in receipt['command'] and '-M4400' in receipt['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source.read_text(),re.M)
 for report in receipt['print_axioms']:
  match=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert match and set(re.findall(r'[A-Za-z_.]+',match[1]))<={'propext','Classical.choice','Quot.sound'}
for name,h in load(E/'s1-native-word-control-tool-pins.json')['scripts'].items():assert sha(R/name)==h
for name,h in load(E/'s1-native-word-control-reused-pins.json')['packets'].items():assert sha(E/name)==h
print(json.dumps(dict(seven_normal_return_cases=True,normal_Rust_rejection_prefix_control=True,exact_numeric_call_order=True,checks=count,wall_seconds=wall,peak_rss_kib=peak,swaps=0,baseline_reference_emission_reused=True,actual_numeric_leaf_interpretation=False,abort_transport=False,whole_s1_closed=False)))
