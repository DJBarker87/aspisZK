#!/usr/bin/env python3
"""Audit the conditional source generalization; never report deleted joins."""
import hashlib,json,pathlib,difflib
HERE=pathlib.Path(__file__).resolve().parent
LEAN=HERE.parent/'lean/R1Z'
old=(LEAN/'PrivacyR1FinalRelease.lean').read_text()
new=(LEAN/'PrivacyR1FinalReleaseSource.lean').read_text()
def statement(s,name):
 a=s.index('theorem '+name+'\n');b=s.index(' := by',a)
 return s[a:b]
before=statement(old,'privacy_R1_release')
after=statement(new,'privacy_R1_release_source')
added='    (R_source_records_admission_banks_transport : BuilderRuntimeJoin.RustRuntimeJoin h)\n'
assert after.count(added)==1
assert after.replace('theorem privacy_R1_release_source','theorem privacy_R1_release',1).replace(added,'')==before
assert 'local notation "h" => (BuilderSource.prover («K» := K))' in old
assert '(h : HonestProver K)' in new
assert before.split(' :\n    ZK_FSS',1)[1]==after.split(' :\n    ZK_FSS',1)[1]
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
result=dict(before_sha256=sha(old),after_sha256=sha(new),removed_binders=[],added_binders=['R_source_records_admission_banks_transport'],context_change='h changes from fixed BuilderSource.prover to arbitrary HonestProver K; the new explicit runtime join is uninhabited for the shipped prover.',other_binders_and_conclusion_verbatim_equal=True,
 real_execution_premise_removed=False,ideal_execution_premise_removed=False,
 status='Conditional source-facing generalization, not a stronger release closure or a claim that the added source premise is weaker than the canonical theorem.',
 signature_diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='PrivacyR1FinalRelease',tofile='PrivacyR1FinalReleaseSource')))
(HERE/'builder-cont6-signature-audit.json').write_text(json.dumps(result,indent=2)+'\n')
marker='## D99 continuation 6: source-facing endpoint and exact signature difference'
p=HERE/'PRIVACY-RELEASE-20261021.md'
s=p.read_text()
if marker in s:s=s[:s.index(marker)].rstrip()+'\n'
s+='\n'+marker+'''\n
`PrivacyR1FinalReleaseSource.privacy_R1_release_source` is a conditional
source-facing generalization with the same freshness allowance and <2^-100
conclusion. The original canonical release theorem is unchanged. The new
endpoint takes an arbitrary honest prover h and an explicit
`R_source_records_admission_banks_transport : RustRuntimeJoin h`.
No inhabitant of that join for shipped Rust is claimed.

**No remaining D99 release premise is deleted by continuation 6.** The exact
real `ModelExecutionJoin` and ideal `ModelExecutionJoin` binders stay
verbatim, as do all commitment premises and the entire conclusion. The new
record and bank proofs narrow implementation obligations, but do not imply
those execution joins. This is not presented as an assumption reduction:
h was fixed to the canonical builder before, and is an input afterwards.
The checked assembly of builder soundness/public membership from RuntimeJoin
is reused from D96; it is not newly asserted to identify the shipped source.

`builder-cont6-signature-audit.py` checks that deleting only the displayed
new binder and restoring the theorem name reproduces the old statement
byte-for-byte. It records the h-context change separately. Before context:
`local notation "h" => (BuilderSource.prover («K» := K))`.
After context: `(h : HonestProver K)`.

The new `BuilderExecutionBoundary.no_constant_mismatch_join` proves that
constant-zero and constant-one observations cannot admit a fixed-event
ModelExecutionJoin when the model bad-event union has mass <1. Thus deleting
the real execution premise for an arbitrary `source : FSExperiments` cannot
follow from builder soundness alone. This is an obstruction to that generic
inference, not a counterexample to privacy of the shipped prover.

The actual remaining source obligations are: successful forest semantic
admission (the isolated higher-ranked callback lifetime blocks the direct
translation route); Parts content equal to the canonical writer composition;
final Vec/column wrapping and the concrete source h/transport; and actual
checker/no-pole/tape/retry/error/publication/serialization/oracle-history
execution with the required uniform coupling. See
`BUILDER-CONT6-20261021.md` and `builder-cont6-extraction.json` for the exact
proved boundary, source pins and retained failures. Neither arbitrary bad
events nor a source experiment defined equal to the model is used.

Verbatim before statement (in the fixed canonical-h context):

```lean
'''+before+'''
```

Verbatim after statement (in the arbitrary-h context):

```lean
'''+after+'''
```
'''
p.write_text(s)
print('PASS: no binder removed; one explicit runtime join added with arbitrary h; all other binders and conclusion byte-identical')
