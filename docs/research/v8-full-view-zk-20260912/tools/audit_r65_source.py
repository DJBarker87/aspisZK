#!/usr/bin/env python3
"""Authenticate the checked CM31 closure; no compiler-correctness claim."""
import hashlib, json, re
from pathlib import Path

CHECKED = {
 'generated/AspisR65Field/Types.lean': '94db6c53943ea6a2f8597b3508b096fbc123984b816a549c75aa5fd17726b8ff',
 'generated/AspisR65Field/Funs.lean': '13cef0ccd8b41a55910ddb6c09691c2aececd0008756764f5878f7062cc8c9d9',
 'generated/translation.json': '854e3dfb32d7c4dfd4985b942ea5813534d2bb6e51d90be776dbc001edf7f0e3',
 'R65Field.llbc': '0106be4ac9bac6f09319a84bd4860de01773cce9c89beeb34812f9626dd6c533'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def body(s):
    assert s.count('namespace AspisR65Field\n') == s.count('end AspisR65Field') == 1
    return s.split('namespace AspisR65Field\n')[1].split('\nend AspisR65Field')[0]
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
    assert all(x in commands[1]['command'] for x in ['--release','--locked','--offline','crate::complex_inverse_probe'])
    meta = json.loads((extraction/'generated/translation.json').read_text())
    assert len(meta['functions']) == 11 and len(meta['types']) == 2 and len(meta['globals']) == 1
    assert not meta['trait_decls'] and not meta['trait_impls']
    assert all(r['is_local'] and not r['is_opaque'] for r in meta['functions'])
    types = (extraction/'generated/AspisR65Field/Types.lean').read_text()
    funs = (extraction/'generated/AspisR65Field/Funs.lean').read_text()
    text = sliced.read_text(); slice_check(types,funs,text)
    changes = [('self + rhs','self - rhs'), ('self = 0#u32','self != 0#u32'),
      ('field.P - self','self - field.P'), ('mul self.b self.b','mul self.a self.b'),
      ('add m m1','add m m'), ('inverse norm','inverse self.a'),
      ('neg self.b','neg self.a'), ('(field.M31.inv)','(fun x => ok x)')]
    for old,new in changes:
        mutated = text.replace(old,new,1); assert mutated != text
        try: slice_check(types,funs,mutated)
        except AssertionError: pass
        else: raise AssertionError('accepted generated mutation')
    return {'checked_profile':True, 'extraction_pins':pins, 'source_stage_pins':len(manifest['files']),
      'local_functions_nonopaque':11, 'negative_mutations_rejected':len(changes),
      'slice_sha256':sha(sliced), 'scope':'generated checked execution; not a verified compiler'}
