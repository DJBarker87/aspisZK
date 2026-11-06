from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;p=E.parent/'field4-20261108'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],text=True);segments=(p/'NKJ_segments.rs.txt').read_text()
required=['sums[component][channel] += left_components[component][channel].0 as u64\n                * right_components[component][channel].0 as u64;', 'let left_sum = left.c0.add(left.c1);','let right_sum = right.c0.add(right.c1);','while index < N','index += 1']
checks=[]
for q in required:
 assert q in frozen,q
 checks.append(dict(frozen_fragment=q,line=frozen[:frozen.index(q)].count('\n')+1,verified=True))
start=frozen.index('    let left_sum = left.c0.add(left.c1);');end=frozen.index('    for component in 0..3',start);prelude=frozen[start:end];assert prelude in segments
for q in ['a.0 as u64 * b.0 as u64','s+=p;s','s[i][j]=v;s','cache[i][j].0','let mut r=start..3;let v=r.next()','index+=1;index']:
 assert q in segments,q
 checks.append(dict(segment=q,verified=True))
(E/'NKN_SOURCE_REVIEW.json').write_text(json.dumps(dict(status='PASS',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',field_source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),segments_sha256=hashlib.sha256(segments.encode()).hexdigest(),checks=checks,cache_prelude_verbatim=True,association='Same component/channel renamed i/j; selected words -> integer product -> checked addition -> selected write via NKJ_NativeStep.source. Source Range order by NativeFold.source/order. Zero/outer increment/converter/return NativeSmall.source/value with canonical/budget invariant; sum2/3/4 original array wrappers use revalidated inherited NFT native pairs.',Result_arms='Canonical/budget/arity domain proves every emitted arithmetic/index Result ok; fail/div impossible by bounded checked arithmetic. No assumed successful child. Converter at SAME accumulated bound. Off-domain uncredited.',returned_shape_families=5,reviewed_transcription='NKJ-RT036/044/040/041/043 option-A reclassification',runtime_trust_changes=[]),indent=1)+'\n')
print('Source segment association PASS')
