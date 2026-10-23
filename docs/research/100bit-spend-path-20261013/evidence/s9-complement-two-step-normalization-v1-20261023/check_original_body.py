from pathlib import Path
import re,hashlib,json
W=Path(__file__).resolve().parent
raw=(W/'original-extraction/Funs.lean').read_text()
model=(W/'sources/S9ComplementTwoStepNormalizationV1.lean').read_text()
a=raw.index('def state_only_prefix.state_only_statement_points_loop1.body')
b=raw.index(':= do',a)+len(':= do')
c=raw.index('/--',b)
original=raw[b:c].strip()
original=original.replace('core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next','next')
a=model.index('def body '); b=model.index(':= do',a)+len(':= do');c=model.index('def run ',b)
checked=model[b:c].strip()
norm=lambda x:re.sub(r'\s+','',x)
assert norm(original)==norm(checked),'emitted original body differs beyond explicit iterator slot'
receipt=json.loads((W/'original-extraction/receipt.json').read_text())
assert receipt['exit_status']==0
assert hashlib.sha256((W/'original-extraction/Funs.lean').read_bytes()).hexdigest() in receipt['generated_lean'].values()
assert not list(W.rglob('*.olean'))
print('PASS: emitted original complement body matches checked body after explicit iterator-next parameter; concrete iterator correspondence OPEN')
