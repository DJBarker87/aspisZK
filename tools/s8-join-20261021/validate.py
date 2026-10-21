#!/usr/bin/env python3
"""Validate S8 pins/receipts without a solver replay or changing old packets."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s8-join-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((B/'evidence/s8-kani-20261021/source-binding.json').read_text())
for name,digest in frozen['source_files'].items():
 assert sha(R/name)==digest,name
for name,digest in frozen['reference_sources'].items():
 assert sha(R/'tools/s8-kani-20261021'/name)==digest,name
reuse=json.loads((B/'evidence/s8-kani2-20261021/mutable-source-reuse.json').read_text())
mapping={str(Path(d['retained_source']).with_suffix('')).split('/sources/')[1].replace('/','.'):name for name,d in reuse.items()}
def tokens(s):return re.sub(r'^#print axioms [^\n]+','',s,flags=re.M).split()
for name,d in reuse.items():
 source=R/d['retained_source'];assert sha(source)==d['sha256']
 expected=source.read_text()
 for old,new in mapping.items():expected=expected.replace('import '+old,'import '+new)
 if name=='S8Kani2PendingWrite':expected+='\nend batched_weights\nend AspisR1BatchedWeightsFinishExtraction\n'
 expected=expected.replace('AspisR1BatchedWeightsFinishExtraction','S8Kani2MutableExtraction').replace('BwPrefixWriteIndex','S8Kani2PrefixWriteIndex').replace('BwSliceSetIndexLemmas','S8Kani2SliceSetIndexLemmas')
 assert tokens(expected)==tokens((B/'lean'/(name+'.lean')).read_text()),name
accepted={};attempts=[]
for p in sorted((E/'proofs').glob('*/receipt.json')):
 d=json.loads(p.read_text());assert sha(p.with_name('source.lean'))==d['source_sha256']
 assert d['swaps']==0
 attempts.append(dict(receipt=str(p.relative_to(E)),module=d['module'],exit_status=d['exit_status']))
 if d['exit_status']:continue
 assert d['print_axioms'],p
 for audit in d['print_axioms']:
  if 'depends on axioms:' in audit:
   names=set(re.findall(r'\b[A-Za-z][A-Za-z_.]*\b',audit.split('depends on axioms:')[1]))
   assert names<={'propext','Classical.choice','Quot.sound'},(p,names)
 source=B/'lean'/(d['module'].replace('.','/')+'.lean')
 if source.exists() and sha(source)==d['source_sha256']:accepted[d['module']]=d
for source in sorted((B/'lean').glob('S8Join*.lean')):
 assert source.stem in accepted,source
 text=source.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),source
 for theorem in re.findall(r'^(?:private )?theorem\s+(\w+)',text,re.M):
  assert '#print axioms '+theorem in text,(source,theorem)
changed=subprocess.check_output(['git','diff','--name-only','6c520f134','--','crates','programs'],cwd=R,text=True).splitlines()
assert not changed,changed
upstream=json.loads((E/'upstream-s7.json').read_text())
assert hashlib.sha256(subprocess.check_output(['git','show',upstream['commit']+':'+upstream['source']],cwd=R)).hexdigest()==upstream['source_sha256']
assert sha(Path(upstream['object_path']))==upstream['object_sha256']
headline='docs/research/100bit-spend-path-20261013/lean/OraclePortFrozenOrderHeadline.lean'
assert (R/headline).read_bytes()==subprocess.check_output(['git','show','6c520f134:'+headline],cwd=R)
unique={line.split("'")[1] for d in accepted.values() for line in d['print_axioms']}
report=dict(unique_theorems=len(unique),headline_sha256=sha(R/headline),headline_change='none',upstream_s7_commit=upstream['commit'],schema='focused-extractor-proof-packet-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),frozen_source_files=frozen['source_files'],reused_mutable_models=list(reuse),accepted_modules=sorted(accepted),accepted_theorem_audits=sum(len(d['print_axioms']) for d in accepted.values()),peak_rss_bytes=max(d['peak_rss_bytes'] for d in accepted.values()),swaps=0,shipped_changes=changed,attempts=attempts)
(E/'accepted-summary.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['accepted_modules','unique_theorems','accepted_theorem_audits','peak_rss_bytes','swaps','shipped_changes']},indent=2))
