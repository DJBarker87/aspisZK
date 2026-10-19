import hashlib, re, sys
from pathlib import Path
adapter, certificate = map(Path, sys.argv[1:3])
expected_adapter = 'f1c1765883a09cc9d9ec926127efbd3810f9f60cf5c77893d35b633e5288bb3f'
assert hashlib.sha256(adapter.read_bytes()).hexdigest() == expected_adapter
line = next(x for x in adapter.read_text().splitlines()
            if x.startswith('def fast_domain.TABLE_A_chunk_00'))
pairs = [tuple(map(int, p)) for p in
         re.findall(r'\((\d+)#u32, (\d+)#u32\)', line)]
assert len(pairs) == 32
text = certificate.read_text()
for i, (a, b) in enumerate(pairs):
    stmt = (f'theorem entry_{i:02d} :\n'
            '    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen\n'
            f'      (R17TableExponentDomainBridge.leftExponent {i}) = ⟨{a}, {b}⟩')
    assert stmt in text, (i, stmt)
print('verified 32 ordered A chunk entries against source-pinned adapter')
