#!/bin/bash
# usage: bash PCXC_gen_walk.sh OUT.lean "import A\nimport B" "root1,root2"   (targets are the 8 NO_FROZEN_COUNTERPART gate definitions)
cd "$(dirname "$0")"
python3 -I -B - "$1" "$2" "$3" <<'PY'
import sys
out, imports, roots = sys.argv[1], sys.argv[2].replace('\\n', '\n'), sys.argv[3].split(',')
T = ['AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value','AspisR72Sampler.field.r23_product_u32_bounded','AspisR72Sampler.field.r24_canonical_mul','AspisR72Sampler.field.r24_canonical_mul.PP','AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call','AspisR72Sampler.field.r24_canonical_mul.closure','AspisR1ClaimsUnrolledParent.candidate_claims.claims','NJT_ClaimsRef.r1_semantic.NJT_claims_ref']
t = open('PCXC_WalkTemplate.lean.in').read()
tg = ', '.join('`' + x for x in T)
an = '\n'.join(f'  analyse env `{r} targets' for r in roots)
open(out, 'w').write(t.replace('@@IMPORTS@@', imports).replace('@@TARGETS@@', tg).replace('@@ANALYSES@@', an))
PY
