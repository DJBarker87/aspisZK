#!/usr/bin/env python3
"""Check exact generated checked_q/from_limbs bodies modulo named callback parameterization."""
from pathlib import Path
import hashlib, json, re

RAW = Path('/tmp/eby-k-push-cut-v3/generated/AspisR1EbyKPushCutV3/Funs.lean')
ADAPTED = Path('/tmp/EbyKCheckedQAllParamV1.lean')

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def generated_body(text, marker):
    start = text.index(marker)
    end = text.find('\n/--', start + len(marker))
    chunk = text[start:end if end >= 0 else len(text)]
    return chunk.split(':= do', 1)[1].strip()

def local_body(text, marker, next_marker):
    start = text.index(marker)
    end = text.index(next_marker, start + len(marker))
    return text[start:end].split(':= do', 1)[1].strip()

def norm(s):
    # Tokenization disregards formatting while retaining every identifier/operator/token.
    return ' '.join(re.findall(r'[A-Za-z_][A-Za-z0-9_\'.]*|[0-9]+#[A-Za-z0-9_]+|[0-9]+|[^\s]', s))

raw = RAW.read_text()
adapted = ADAPTED.read_text()

checks = {}

# The limb constructor is copied verbatim except for namespace-local naming and
# harmless spacing in the array literal.
rb = generated_body(raw, 'def fast_pairing.limbs_of')
lb = local_body(adapted, 'def limbsOf', '\ndef fromLimbsWithAll')
checks['limbs_of_body'] = norm(rb) == norm(lb)

# The iterator's only substitution is replacing the generated external call to
# Iterator::all and its generated closure instance with explicit parameters and
# the locally reproduced generated closure value.
rb = generated_body(raw, 'def fast_pairing.canonical.Q.from_limbs')
rb = rb.replace('core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all', 'all')
rb = rb.replace('fast_pairing.canonical.Q.from_limbs.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool', 'fromLimbsClosureFnMut')
lb = local_body(adapted, 'def fromLimbsWithAll', '\ndef optionOkOr')
checks['from_limbs_body_all_parameterized'] = norm(rb) == norm(lb)

# checked_q differs only by passing the explicit all callback through the
# parameterized from_limbs adapter. The error conversion is named optionOkOr.
rb = generated_body(raw, 'def fast_pairing.checked_q')
rb = rb.replace('fast_pairing.limbs_of', 'limbsOf')
rb = rb.replace('fast_pairing.canonical.Q.from_limbs a', 'fromLimbsWithAll all a')
rb = rb.replace('core.option.Option.ok_or', 'optionOkOr')
lb = local_body(adapted, 'def checkedQWithAll', '\nprivate theorem result_bind_ok_inv')
checks['checked_q_body_all_parameterized'] = norm(rb) == norm(lb)

if not all(checks.values()):
    for k,v in checks.items(): print(k, v)
    raise SystemExit(1)

out = {
  'result': 'pass',
  'checks': checks,
  'generated_funs': {'path': str(RAW), 'sha256': sha(RAW)},
  'adapted_lean': {'path': str(ADAPTED), 'sha256': sha(ADAPTED)},
  'scope': 'Exact emitted limbs_of/from_limbs/checked_q bodies, modulo only explicit Iterator.all parameterization, generated-name localization, and the corresponding callback argument insertion.'
}
print(json.dumps(out, indent=2))
