#!/usr/bin/env python3
"""Authenticate the checked extraction and its exact narrowed declaration slice."""
import argparse, hashlib, json, re
from pathlib import Path

CHECKED={
 'generated/AspisR64Field/Types.lean':'49f7423d46c9a89c93e986cd74dd48ff51c0df00ac19c245f64386537eead35e',
 'generated/AspisR64Field/Funs.lean':'6a391404ad5afbcaff3046f91d7885f531ac913ca60a4a60da9d8173148721a7',
 'generated/translation.json':'b2036bef0a46ba7a7391cd434034337cc646a96d663605b3dac637670ee47293',
 'R64Field.llbc':'4b0e277bf34236edc524a2731351be81d44d8070a57ff35570482e2376f0795d'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def body(s):
    assert s.count('namespace AspisR64Field\n')==1 and s.count('end AspisR64Field')==1
    return s.split('namespace AspisR64Field\n',1)[1].split('\nend AspisR64Field',1)[0].strip()
def slice_check(types,funs,sliced):
    t=body(types);t=t[t.index('@[reducible]'):].rstrip()
    assert body(sliced)==t+'\n'+funs.split('namespace AspisR64Field\n',1)[1].split('\nend AspisR64Field',1)[0].rstrip()
    assert not re.search(r'\b(sorry|axiom|opaque|native_decide)\b',body(sliced))
    assert len(re.findall(r'\bdef (?:field\.[\w.]+|inverse_probe)\b',body(sliced)))==9
def check_current(extraction,sliced,stage,kit):
    pins=json.loads((extraction/'pins.json').read_text());assert len(pins)==11
    for n,h in pins.items():assert sha(extraction/n)==h,n
    for n,h in CHECKED.items():assert pins[n]==h,n
    manifest=json.loads((stage/'r18-stage.json').read_text())
    for name in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
        assert sha(extraction/'source'/name)==manifest['files']['crates/aspis-core/src/'+name],name
    for name in ['Cargo.toml','lib.rs']:assert sha(kit/name)==sha(extraction/'source'/name)
    env=json.loads((extraction/'environment.json').read_text())
    assert env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true' and env['RUSTUP_TOOLCHAIN']=='nightly-2026-06-01'
    commands=json.loads((extraction/'commands.json').read_text())
    assert [r['label'] for r in commands]==['lock','extract','translate'] and all(r['exit']==0 for r in commands)
    assert '--release' in commands[1]['command'] and '--locked' in commands[1]['command'] and '--offline' in commands[1]['command']
    meta=json.loads((extraction/'generated/translation.json').read_text())
    assert len(meta['functions'])==7 and len(meta['types'])==1 and len(meta['globals'])==1
    assert not meta['trait_decls'] and not meta['trait_impls']
    assert all(r['is_local'] and not r['is_opaque'] for r in meta['functions'])
    types=(extraction/'generated/AspisR64Field/Types.lean').read_text()
    funs=(extraction/'generated/AspisR64Field/Funs.lean').read_text()
    text=sliced.read_text();slice_check(types,funs,text)
    changes=[('self < field.P','self <= field.P'),('rhs < field.P','rhs <= field.P'),
      ('let x ← i * i1','let x ← i + i1'),('31#i32','30#i32'),
      ('s - i6','s + i6'),('UScalar.cast .U32 i7','UScalar.cast .U32 s'),
      ('let i3 ← field.reduce_u64 i2','let i3 ← field.reduce_u64 0#u64'),
      ('self != 0#u32','self == 0#u32'),('square_n t16 8#usize','square_n t16 7#usize')]
    for old,new in changes:
        mutated=text.replace(old,new,1);assert mutated!=text
        try:slice_check(types,funs,mutated)
        except AssertionError:pass
        else:raise AssertionError('accepted generated mutation')
    return {'extraction_pins':pins,'checked_profile':True,'source_stage_pins':len(manifest['files']),
      'declarations_byte_identical':9,'local_functions_nonopaque':7,'negative_mutations_rejected':9,
      'slice_sha256':sha(sliced),'scope':'generated checked execution under the pinned extraction/runtime model; not a verified Rust compiler'}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    for n in ['extraction','slice','stage','kit']:p.add_argument('--'+n,type=Path,required=True)
    a=p.parse_args();print(json.dumps(check_current(a.extraction,a.slice,a.stage,a.kit),indent=2))
