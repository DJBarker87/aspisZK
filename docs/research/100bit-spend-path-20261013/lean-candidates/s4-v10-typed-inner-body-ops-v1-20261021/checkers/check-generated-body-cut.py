#!/usr/bin/env python3
from pathlib import Path
import textwrap
repo = Path(__file__).resolve().parents[6]
generated = repo / 'docs/research/100bit-spend-path-20261013/lean-candidates/s4-minimal-fixed-calls-v10-20261021/extraction/evidence/transparent-carriers-aeneas-v1/generated/AspisR1FastDotsMinimalFixedCallsV10/Funs.lean'
cut = Path(__file__).resolve().parents[1] / 'sources/S4V10TypedInnerBodyOpsV1.lean'
s = generated.read_text()
mark = 'def fast_dots.four_dots_one_loop0_loop0.body\n'
i = s.index(mark)
j = s.index('/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop 1:', i)
body = s[i:j]
body = body[body.index(':= do') + len(':= do'):].strip()
body = body.replace('aspis_core.field.M31.from_le_bytes a', 'ops.m31FromBytes a')
body = body.replace('aspis_core.field.wide_exact.WideExact.to_limbs we', 'ops.wideToLimbs we')
t = cut.read_text()
mark2 = 'def v10TermBody\n'
i2 = t.index(mark2)
j2 = t.index('\n\nend AspisR1FastDotsV10TypedInnerBodyOpsV1', i2)
cutbody = t[i2:j2]
cutbody = cutbody[cutbody.index(':= do') + len(':= do'):].strip()
cutbody = cutbody[:cutbody.index('ok (cont (iter1, sums8))') + len('ok (cont (iter1, sums8))')]
if textwrap.dedent(cutbody) != textwrap.dedent(body):
    raise SystemExit('typed cut body differs from emitted V10 body outside the two explicit operation slots')
if t.count('ops.m31FromBytes a') != 1 or t.count('ops.wideToLimbs we') != 1:
    raise SystemExit('expected exact parser and wide-to-limbs operation slots')
print('PASS: body is emitted V10 term-body verbatim modulo the two explicit operation slots')
