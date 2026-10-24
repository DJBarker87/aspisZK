#!/usr/bin/env python3
"""Source-only API audit: explicitly excludes any native proof conclusion."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];P=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-init-api-assessment-20261024'
m=json.loads((P/'manifest.json').read_text());assert m['external_revision']=='4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d'
for row in m['sources']:
 p=P/'sources'/row['path'];assert p.stat().st_size==row['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
mem=(P/'sources/library/kani_core/src/mem.rs').read_text();compiler=(P/'sources/kani-compiler/src/kani_middle/transform/kani_intrinsics.rs').read_text()
a=mem.index('pub fn can_dereference');b=mem.index('/// Checks that pointer',a)
assert '&& assert_is_initialized(ptr)' in mem[a:b]
assert 'pub(crate) fn is_initialized' in mem
start=compiler.index('fn is_initialized_body');end=compiler.index('// Instead of injecting the instrumentation',start)
assert 'if !self.enable_uninit' in compiler[start:end] and 'MirConst::from_bool(true)' in compiler[start:end] and 'return new_body.into()' in compiler[start:end]
assert 'FieldsShape::Primitive with a different ABI than ValueAbi::Scalar' in (P/'sources/kani-compiler/src/kani_middle/transform/check_uninit/ty_layout.rs').read_text()
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',kind='source-inspection-only',native_initializedness_proved=False,mem_predicates_without_uninit_sufficient=False)))
