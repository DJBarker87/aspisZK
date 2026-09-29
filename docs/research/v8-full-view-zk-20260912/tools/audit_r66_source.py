#!/usr/bin/env python3
"""Authenticate the checked QM31 closure; no compiler-correctness claim."""
import hashlib, json, re
from pathlib import Path

CHECKED = {
 'generated/AspisR66Field/Types.lean': '2433db0496ad548f2a1ffd2bd632c842daed6086f6656d7bb9959fbefdd7c6ad',
 'generated/AspisR66Field/Funs.lean': '74b0f6ca419ac7cb147e539b849ff0a31006d00be950f0b83b312fda12b4622a',
 'generated/translation.json': '6e9b3493c76234b93eab544c410ae84b04ee3599c4f9c491414a22abde51b15c',
 'R66Field.llbc': 'b1fdd1f9669fd9b8236eb263d96da0facd6da48016707fe1ab84733912fe26d2'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def body(s):
    assert s.count('namespace AspisR66Field\n') == s.count('end AspisR66Field') == 1
    return s.split('namespace AspisR66Field\n')[1].split('\nend AspisR66Field')[0]
def slice_check(types, funs, sliced):
    assert body(sliced) == body(types) + body(funs)
    assert not re.search(r'\b(sorry|axiom|opaque|native_decide)\b', body(sliced))
def check_current(extraction, sliced, stage, kit):
    pins = json.loads((extraction/'pins.json').read_text())
    assert len(pins) == 11
    for n, h in pins.items(): assert sha(extraction/n) == h, n
    for n, h in CHECKED.items(): assert pins[n] == h, n
    manifest = json.loads((stage/'r18-stage.json').read_text())
    for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
        assert sha(extraction/'source'/n) == manifest['files']['crates/aspis-core/src/'+n]
    for n in ['Cargo.toml','lib.rs']: assert sha(kit/n) == sha(extraction/'source'/n)
    env = json.loads((extraction/'environment.json').read_text())
    assert env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS'] == 'true'
    assert env['RUSTUP_TOOLCHAIN'] == 'nightly-2026-06-01'
    commands = json.loads((extraction/'commands.json').read_text())
    assert [r['label'] for r in commands] == ['lock','extract','translate']
    assert all(r['exit'] == 0 for r in commands)
    assert all(x in commands[1]['command'] for x in ['--release','--locked','--offline','crate::quartic_inverse_probe'])
    meta = json.loads((extraction/'generated/translation.json').read_text())
    assert len(meta['functions']) == 24 and len(meta['types']) == 3 and len(meta['globals']) == 1
    assert not meta['trait_decls'] and not meta['trait_impls']
    assert all(r['is_local'] and not r['is_opaque'] for r in meta['functions'])
    types = (extraction/'generated/AspisR66Field/Types.lean').read_text()
    funs = (extraction/'generated/AspisR66Field/Funs.lean').read_text()
    text = sliced.read_text(); slice_check(types,funs,text)
    changes = [('self + rhs','self - rhs'), ('self = 0#u32','self != 0#u32'),
      ('field.P - self','self - field.P'), ('mul self.b self.b','mul self.a self.b'),
      ('add m m1','add m m'), ('inverse norm','inverse self.a'),
      ('neg self.b','neg self.a'), ('(field.M31.inv)','(fun x => ok x)'),
      ('UScalar.cast .U32 left','UScalar.cast .U32 right'),
      ('let i9 ← i7 - i8','let i9 ← i7 + i8'),
      ('field.CM31.is_zero self.c1','field.CM31.is_zero self.c0'),
      ('field.mul_by_r c1','field.mul_by_r c')]
    for old,new in changes:
        mutated = text.replace(old,new,1); assert mutated != text
        try: slice_check(types,funs,mutated)
        except AssertionError: pass
        else: raise AssertionError('accepted generated mutation')
    return {'checked_profile':True, 'extraction_pins':pins, 'source_stage_pins':len(manifest['files']),
      'local_functions_nonopaque':24, 'negative_mutations_rejected':len(changes),
      'slice_sha256':sha(sliced), 'scope':'generated checked execution; not a verified compiler'}
