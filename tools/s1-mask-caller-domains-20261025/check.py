#!/usr/bin/env python3
"""Read-only mask caller/source-domain packet check; never replays compilers."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-mask-caller-domains-20261025';T=Path(__file__).parent;S=B/'lean-candidates/s126-caller-boundary-20261021';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.ir','.goto','.out','.rlib','.rmeta','.o','.a','.so'],rel
for script in ['materialize-sdk.py','materialize-reached-sdk.py','materialize-canonical-sdk.py','prepare-support.py']:
 q=subprocess.run([sys.executable,str(T/script),'--check'],cwd=R,capture_output=True,text=True);assert q.returncode==0,q.stdout+q.stderr
bindings=json.loads((T/'mask-factor-binding.json').read_text());base=(R/bindings['base']).read_text();target=(R/bindings['target']).read_text();assert sha(R/bindings['base'])==bindings['base_sha256'] and sha(R/bindings['target'])==bindings['target_sha256'];a=base.index('abbrev ProbeQM');b=base.index('\ndef add',a);c=base.index('def mask (');d=base.index('\n/-- Six concrete',c)
for chunk,h in zip([base[a:b],base[c:d]],bindings['exact_source_chunks']):assert chunk in target and hashlib.sha256(chunk.encode()).hexdigest()==h
assert 'abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31' in target
assert '{B with fromFn :=' in target and 'mask := mask}' in target
# All accepted declarations are actually checked with current exact sources.
metrics=json.loads((P/'metrics.json').read_text());allrows=metrics['new_targets']+metrics['support_targets'];audits=0
for row in allrows:
 d=E/row['attempt'];j=json.loads((d/'receipt.json').read_text());module=j['target'];source=R/row['source']
 assert j['exit_status']==0 and j['swaps']==0 and j['source_sha256']==sha(source)==sha(d/'source.lean')
 assert '-j1' in j['command'] and '-M4400' in j['command'] and j['print_axioms']
 assert not re.search(r'(?m)^\s*axiom\b|\b(sorry|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',source.read_text())
 for audit in j['print_axioms']:
  assert 'sorryAx' not in audit
  found=re.findall(r'\[(.*?)\]',audit,re.S)
  if found:assert set(found[0].replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'},audit
 audits+=len(j['print_axioms'])
assert len(allrows)==32 and audits==91
# Strict before/after postconditions: old SDK binders and old conjuncts stay.
def signature(s):return s[s.index(' {W A M Cv : Type}'):s.index(' :\n    post =')]
def post(s):return s[s.index(' :\n    post ='):s.index(' := by')]
a=(S/'S1SdkClaimInputRangesV1.lean').read_text();b=(S/'S1SdkMaskInputRangesV1.lean').read_text();assert signature(a)==signature(b);extra='        AspisS1MaskCallerDomains.MaskInputRanges (retainedSem sem) ∧\n';assert post(a)==post(b).replace(extra,'')
a=(S/'S1SdkReachedMaskInputsV1.lean').read_text();b=(S/'S1SdkCanonicalMaskV1.lean').read_text();assert signature(a)==signature(b)
extra='''        AspisS1ReachedMaskCanonical.ReachedCanonicalMask
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install base))) (retainedSem sem) ∧
''';assert post(a)==post(b).replace(extra,'')
# Failures remain failures, including the bounded import-memory stop.
j=json.loads((E/'s1-reached-mask-inputs-v1/receipt.json').read_text());assert j['exit_status']==134 and not j['print_axioms'];assert 'lean::memory_exception' in (E/'s1-reached-mask-inputs-v1/time.log').read_text()
assert json.loads((E/'s1-reached-mask-inputs-v2/preflight.json').read_text())['compiler_launched']is False
# Reused native selector/source equality evidence: source-only read-only check.
q=subprocess.run([sys.executable,str(R/'tools/s1-finish-children-20261024/check.py')],cwd=R,capture_output=True,text=True);assert q.returncode==0,q.stderr
assert json.loads(q.stdout)['native_checks']==467
print(f'PASS {len(m["files"])} pins, 32 focused targets/91 standard-only audits. Actual reached mask input/output numeric obligations derived at SAME conditional SDK/source boundary; original SDK/native/extraction/SourceCuts and other finish gates remain. S1/S6 and 100-bit target NOT established.')
