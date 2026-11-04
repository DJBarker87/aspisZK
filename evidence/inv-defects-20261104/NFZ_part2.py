"""Compile-free accounting of terminal part-2 compiler attempts; no edge credit."""
from pathlib import Path
import json,lzma,hashlib,collections,base64,subprocess,posixpath,re
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda n:json.loads((E/n).read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
# Validate every reconstructed payload against the immutable frozen Git object.
pins=J('NFZ_SOURCE_PINS.json');text=json.loads(lzma.open(E/'NFZ_FROZEN_SOURCE.json.xz').read());binary=json.loads(lzma.open(E/'NFZ_FROZEN_BINARY.json.xz').read());files={**{p:t.encode() for p,t in text.items()},**{p:base64.b64decode(t) for p,t in binary.items()}}
for p,data in files.items():
 assert sha(data)==pins['files'][p]
 assert data==subprocess.check_output(['git','show',pins['revision']+':'+p],cwd=R)
includes=[]
for p,t in text.items():
 for rel in re.findall(r'include(?:_str|_bytes)?!\s*\(\s*"([^"]+)"',t):
  q=posixpath.normpath(posixpath.dirname(p)+'/'+rel);assert q in files
  includes.append(dict(source=p,target=q,sha256=sha(files[q])))
put('NFZ_PAYLOAD_PREFLIGHT.json',dict(result='PASS compile-free only; NOT submitted after scopes exhausted',text_files=len(text),binary_files=len(binary),literal_includes=includes,frozen_revision=pins['revision'],payload_sha256=sha((E/'NFZ_FROZEN_SOURCE.json.xz').read_bytes()),binary_payload_sha256=sha((E/'NFZ_FROZEN_BINARY.json.xz').read_bytes()),pins_sha256=sha((E/'NFZ_SOURCE_PINS.json').read_bytes())))
mir=lzma.open(E/'NFZ_aspis_core.mir.xz').read().decode().splitlines()
def block(location):
 i=next(i for i,l in enumerate(mir) if l.startswith('fn scalar::<impl at ') and location in l and '::from_m31(' in l)
 j=next(j for j in range(i+1,len(mir)) if mir[j].startswith('fn '))
 return i,j,'\n'.join(mir[i:j])
core={}
for loc,expected in [('41:1: 41:23',[]),('56:1: 56:24',['<M31 as CodeField>::from_m31','CM31::from_m31']),('70:1: 70:24',['<CM31 as CodeField>::from_m31','QM31::from_cm31']),('87:1: 87:29',['<QM31 as CodeField>::from_m31','WideExact::from_qm31'])]:
 i,j,t=block(loc);assert all(x in t for x in expected);core[loc]=dict(line_start=i+1,line_end=j,expected_calls=expected)
put('NFZ_CORE_MIR_REVIEW.json',dict(attempt='NFZ_B004',path='NFZ_aspis_core.mir.xz',sha256=sha((E/'NFZ_aspis_core.mir.xz').read_bytes()),blocks=core,claim='Typed function bodies and exact conditional embedding call chain; NOT entry reachability',successful_core_commands=[x for x in map(json.loads,(E/'NFZ_COMPILER_COMMANDS.jsonl').read_text().splitlines()) if x['crate']=='aspis_core' and x['exit']==0]))
c=J('NFZ_CANDIDATES.json');coreids={1,35,36,37,38,39}
for x in c['candidates']:
 n=int(x['id'][5:]);x['admitted']=False
 if n in coreids:
  x.update(compiler_target_resolution='CONFIRMED_IN_CORE_BODY',reachability='UNRESOLVED_ENTRY_PATH',resolution='Core MIR confirms typed embedding calls; absent deployed caller MIR and independent authority prevent occurrence/edge admission',compiler_evidence='NFZ_CORE_MIR_REVIEW.json')
 else:
  x.update(compiler_target_resolution='UNRESOLVED',reachability='UNRESOLVED_REQUIRES_CALLER_MIR',resolution='NFZ_B004 and NFZ_B003 stopped in statement dependency before this caller diagnostic; no source-only edge admitted',compiler_evidence=None)
 x['part2_disposition']='OPEN; no ledger status change'
c.update(authority='Core MIR partial body resolution plus source discovery; no complete entry resolution',complete=False,reason='All three new scopes spent; two input defects and a failed local preflight left caller MIR unavailable',part2_counts=dict(total_candidates=39,core_body_target_resolutions=6,caller_target_resolutions=0,entry_reachability_resolutions=0,admitted=0))
put('NFZ_CANDIDATES.json',c)
mir0=lzma.open(E/'NFZ_aspis_core.mir0.xz').read().decode()
for loc,detail in core.items():
 start=mir0.index('fn scalar::<impl at crates/aspis-core/src/r0/scalar.rs:'+loc+'>::from_m31(')
 end=mir0.index('\nfn ',start+1)
 assert all(call in mir0[start:end] for call in detail['expected_calls'])
ind=J('NFZ_INDEPENDENT_CHECK.json');ind.update(part2_attempt='NFZ_B003',compiler_independent_check_satisfied=False,part2_reason='MIR opt-level 0 and 1 agree on four core embedding bodies and their conditional callee identities. Statement dependency failed before deployed caller MIR; whole-overlay independent authority remains absent.',core_second_MIR_agrees=True,core_second_MIR_sha256=sha((E/'NFZ_aspis_core.mir0.xz').read_bytes()));put('NFZ_INDEPENDENT_CHECK.json',ind)
base=json.loads(lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read());after=json.loads(lzma.open(E/'NFZ_ADMITTED_LEDGER.json.xz').read());assert base==after
cover=J('NFZ_COVERAGE.json');slices=J('NFZ_SLICES.json');orig=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())
delta=J('NFZ_LEDGER_DELTA.json');delta.update(before=base['coverage'],after=after['coverage'],slice_union_before=dict(covered=585,total=587),slice_union_after=dict(covered=cover['counts']['covered'],total=cover['counts']['total']),slice_membership_changes={name:dict(added=sorted(set(slices['slices'][name]['functions'])-set(spec['functions'])),removed=sorted(set(spec['functions'])-set(slices['slices'][name]['functions']))) for name,spec in orig['slices'].items()},QSD_regenerated=True,part2_scope_status='EXHAUSTED: NFZ_B002/B004/B003',new_rows=[],removed_rows=[],status_changes=[],new_closed_rows=[])
put('NFZ_LEDGER_DELTA.json',delta)
summary=[]
for attempt in ['NFZ_B002','NFZ_B004','NFZ_B003']:
 receipt=J(attempt+'/receipt.json');ad=J(attempt+'-admission.json');assert ad.get('allowed',ad.get('reservation',{}).get('allowed')) is True
 for p,h in receipt['source_hashes'].items():assert sha((E/attempt/'sources'/p).read_bytes())==h
 summary.append({k:receipt[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms','limits']})
put('NFZ_PART2_SUMMARY.json',dict(attempts=summary,scope_budget=dict(authorized=3,used=3,remaining=0),Kani=0,Lean=0,extraction=0,compiler_gate_passed=False,independent_authority=False,partial_core_independent_authority=True,source_payload_preflight='PASS after terminal scope failures; unsubmitted',new_rows=0,status_changes=0,coverage=cover['counts']))
print(json.dumps(dict(candidates=39,partial_core_resolutions=6,coverage=cover['counts'],remaining_scopes=0)))
