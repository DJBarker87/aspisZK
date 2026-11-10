#!/bin/bash
# usage: bash PCXC_gen_cone.sh OUT.lean "list1,list2" "RootModule1,RootModule2" "root1,root2"
cd "$(dirname "$0")"
python3 -I -B - "$1" "$2" "$3" "$4" <<'PY'
import sys
out, lists, rmods, roots = sys.argv[1:5]
T = ['AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value','AspisR72Sampler.field.r23_product_u32_bounded','AspisR72Sampler.field.r24_canonical_mul','AspisR72Sampler.field.r24_canonical_mul.PP','AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call','AspisR72Sampler.field.r24_canonical_mul.closure','AspisR1ClaimsUnrolledParent.candidate_claims.claims','NJT_ClaimsRef.r1_semantic.NJT_claims_ref']
t = open('PCXC_ConeWalk.lean.in').read()
q = lambda xs: ', '.join('"%s"' % x for x in xs.split(','))
n = lambda xs: ', '.join('`' + x for x in xs.split(','))
open(out, 'w').write(t.replace('@@LISTS@@', q(lists)).replace('@@ROOTMODS@@', n(rmods)).replace('@@ROOTS@@', n(roots)).replace('@@TARGETS@@', ', '.join('`' + x for x in T)))
PY
