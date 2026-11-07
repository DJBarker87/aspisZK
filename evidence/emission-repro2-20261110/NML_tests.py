"""Negative controls for provenance comparison; no prover/compiler launches."""
import importlib.util
from pathlib import Path
E=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('owned_comparator',E/'NML_compare.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
original=b'import Aeneas\nnamespace NML_X\n@[discriminant isize]\ninductive E where\n| A : E\nend NML_X\n'
normalized=b'import Aeneas\nnamespace NML_X\ninductive E where\n| A : E\nend NML_X\n'
assert m.normalized(original)==normalized
assert m.normalized(original.replace(b'NML_X',b'NML_Y'))!=normalized
assert m.normalized(original.replace(b'| A : E',b'| B : E'))!=normalized
assert m.sha(original)!=m.sha(original+b'\ndef injected := 1\n')
a=m.definitions('def x := 1\ndef y := 2\n');b=m.definitions('def x := 1\ndef y := 3\n')
assert a['x']==b['x'] and a['y']!=b['y']
assert set(m.definitions('def x := 1\n'))!=set(a)
print('PASS: discriminant-only normalization and namespace/body/addition/partial-definition rejection controls')
