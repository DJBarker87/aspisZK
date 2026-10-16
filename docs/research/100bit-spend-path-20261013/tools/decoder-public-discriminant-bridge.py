#!/usr/bin/env python3
"""One-sided naming adapter for the confirmed Decoder/public import collision."""
from pathlib import Path
import argparse
import hashlib
import json

base = Path(__file__).resolve().parents[1]
relative = 'lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Types.lean'
source = base / relative
raw = source.read_bytes()
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha(raw) == '4137560dca226c388376c5d8fe1f30285cc5664d0a86a67184e54212e5bda548'
dest = base / 'lean/bridge-decoder-public-20261016/AspisR1TerminalDecoder/Types.lean'
pins = dest.parent.parent / 'adapter-pins.json'
text = raw.decode()
E = 'pool_v1.payment_relation.PoolV1PaymentStatementFormatError'
marker = '@[discriminant isize]\ninductive ' + E
assert text.count(marker) == 1
ctors = ['WrongLength', 'WrongMagic', 'WrongVersion', 'WrongTransitionKind',
         'WrongDigestEncoding', 'NonZeroReserved', 'ZeroRequiredBinding',
         'InvalidAnchorSequence', 'NonCanonicalDigest', 'NonCanonicalAssetId',
         'InvalidWithdrawalAmount', 'InvalidDestination', 'InvalidEnvelope',
         'EnvelopeMismatch']
end = '| EnvelopeMismatch : ' + E + '\n'
assert text.count(end) == 1
aux = '\n-- Naming-only expansion of the pinned fourteen-code discriminant attribute.\n'
aux += 'def ' + E + '.read_discriminant (x : ' + E + ') : Isize :=\n  match x with\n'
aux += ''.join(f'  | .{c} => {i}#isize\n' for i, c in enumerate(ctors))
aux += '\ninstance _root_.AspisR1TerminalDecoder.' + E + '.instDiscriminant :\n'
aux += '    Aeneas.Std.Discriminant ' + E + ' Isize where\n'
aux += '  read_discriminant := ' + E + '.read_discriminant\n'
adapted = text.replace(marker, 'inductive ' + E).replace(end, end + aux)
assert adapted.replace(aux, '').replace('inductive ' + E, marker) == text
record = {
    'original_source': relative,
    'original_revision': '7e82f16bc13b43400d2b59e9c8fba1530f5f09ad',
    'original_sha256': sha(raw),
    'adapter_source': str(dest.relative_to(base)),
    'adapter_sha256': sha(adapted.encode()),
    'backend_generator_source': 'Aeneas/Data/Discriminant.lean',
    'backend_generator_sha256': '98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03',
    'generator_rule': 'constructor order mapIdx; same read_discriminant; only instance name qualified',
    'old_instance': 'instDiscriminantPoolV1PaymentStatementFormatErrorIsize',
    'new_instance': 'AspisR1TerminalDecoder.' + E + '.instDiscriminant',
    'constructor_codes': [[c, i] for i, c in enumerate(ctors)],
    'inverse_recovers_original_bytes': True,
    'all_other_attributes_unchanged': True,
}
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--check', action='store_true')
args = ap.parse_args()
if args.check:
    assert dest.read_text() == adapted
    assert json.loads(pins.read_text()) == record
    print('PASS: complete inverse; only the fourteen-code payment-error instance name changes')
else:
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(adapted)
    pins.write_text(json.dumps(record, indent=2) + '\n')
    print(dest)
