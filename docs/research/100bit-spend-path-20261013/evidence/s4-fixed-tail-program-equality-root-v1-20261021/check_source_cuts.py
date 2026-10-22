from pathlib import Path
import re
p=Path(__file__).resolve().parent
s=(p/'sources/S4FixedTailProgramEqualityRootV1.lean').read_text()
old=(p/'dependencies/original-FunsOpsV4.lean').read_text();old=old[old.index('  let tail ← ops.ebyKNew',old.index('  fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut\n')):];old=old[:old.index('\n/--')].strip().replace('tupled_args','slot').replace('ok (we2, c)','ok we2')
fixed=(p/'dependencies/fixed-FunsOpsV6.lean').read_text();fixed=fixed[fixed.index('  let tail ← ops.ebyKNew',fixed.index('def fast_dots.four_dots_one\n')):];fixed=fixed[:fixed.index('\n/--')].strip();fixed=re.sub(r'\bg\b','a1',fixed);fixed=re.sub(r'\bq\b','a',fixed)
for name,raw in [('oldTail',old),('fixedTail',fixed)]:
 got=s[s.index(' := do',s.index('def '+name))+len(' := do'):];got=got[:got.index('\n\n')].strip()
 assert re.sub(r'\s+',' ',raw)==re.sub(r'\s+',' ',got),name
print('PASS: exact selected tail programs modulo argument names and old scalar-result projection')
