#!/bin/bash
# X7 gate (vi): grammar of the account write boundaries (X2c's forms D, Z, L, checker unchanged) and of the hash call
# (form H, fv_emit_boundary_check.py --hash), each tool first run on its planted cases. Reads only.
# Usage: fv_emit_gate_grammar.sh <tree dir>
set -u
B=$(cd $(dirname $0) && pwd); S=$1
  echo "== planted cases (X2c's D/Z/L cases, then X7's form-H cases), each must fail except the positives"
bad=0
  for f in $B/fv_emit_negatives/*.rs; do
    case $(basename $f) in h-*) out=$(python3 -I $B/fv_emit_boundary_check.py --hash digest_into $f 2>&1);; *) out=$(python3 -I $B/fv_emit_boundary_check.py $f 2>&1);; esac
    rc=$?; echo "$(basename $f): exit $rc: $(echo "$out" | sed -n 2p)"
    case $(basename $f) in positive-*|h-positive.rs) [ $rc -eq 0 ] || bad=1;; *) [ $rc -ne 0 ] || bad=1;; esac
  done
  echo "== form H text checked by the D/Z/L checker (must not pass)"
  python3 -I $B/fv_emit_boundary_check.py $B/fv_emit_negatives/h-positive.rs > /dev/null 2>&1; rc=$?; echo "exit $rc (non-zero expected)"; [ $rc -ne 0 ] || bad=1
  echo "== the boundary modules of the tree"
  python3 -I $B/fv_emit_boundary_check.py $S/programs/aspis-pool/src/account_write.rs || bad=1
  python3 -I $B/fv_emit_boundary_check.py --only write_zero_data,write_lamports $S/programs/r1-cost-probe/src/r1_pool_adapter.rs || bad=1
  python3 -I $B/fv_emit_boundary_check.py --hash digest_into $S/programs/r1-cost-probe/src/lib.rs || bad=1
  echo "== exact text of each boundary function (sha256 of its lines)"
  python3 -I - $S <<'PY'
import hashlib, re, sys
S = sys.argv[1]
for f, names in (('programs/aspis-pool/src/account_write.rs', ['write_account_data_v1']), ('programs/r1-cost-probe/src/r1_pool_adapter.rs', ['write_zero_data', 'write_lamports']), ('programs/r1-cost-probe/src/lib.rs', ['digest_into'])):
    t = open(S + '/' + f).read(); L = t.split('\n')
    for n in names:
        m = re.search(r'(?m)^[ \t]*(?:#\[inline[^\]\n]*\]\s*\n[ \t]*)?(?:pub(?:\(crate\))?[ \t]+)?fn[ \t]+' + n + r'\b', t)
        a = t.count('\n', 0, m.start()); k = t.index('{', m.end()); d = 0
        while True:
            d += {'{': 1, '}': -1}.get(t[k], 0)
            if d == 0: break
            k += 1
        b = t.count('\n', 0, k)
        txt = '\n'.join(L[a:b + 1]) + '\n'
        print('%s %s lines %d-%d (%d lines) sha256 %s' % (f, n, a + 1, b + 1, b - a + 1, hashlib.sha256(txt.encode()).hexdigest()))
PY
  echo "gate (vi) boundary grammar: $([ $bad -eq 0 ] && echo pass || echo FAIL)"
exit $bad
