#!/usr/bin/env python3
"""Authenticate the generated inverse slice, without claiming a compiler proof."""
import argparse, hashlib, json, re
from pathlib import Path
from check_r17_field_slice import PINS, declaration
from audit_r60_source import audit, clean, function

NAMES=['M31','P','reduce_u64','M31.mul','square_n_loop.body','square_n_loop','square_n','M31.inv']
def validate(sources,text):
    expected=['aspis_core.field.'+n for n in NAMES]
    assert re.findall(r'^(?:def|structure) ([\w.]+)',text,re.M)==expected
    for i,n in enumerate(expected):
        assert declaration(sources['Types.lean' if i==0 else 'FunsChunk04.lean'],n)==declaration(text,n),n

def check(stage,sliced,field,chain):
    sources={}
    for n,h in PINS.items():
        b=(stage/n).read_bytes(); assert hashlib.sha256(b).hexdigest()==h,n
        sources[n]=b.decode()
    text=sliced.read_text(); validate(sources,text)
    mutations=[('31#u32','30#u32'),('let i2 ← i * i1','let i2 ← i + i1'),
      ('start := 0#usize','start := 1#usize'),('M31.mul value value','M31.mul value 0#u32'),
      ('square_n t16 8#usize','square_n t16 7#usize'),('self != 0#u32','self == 0#u32'),
      ('ok (done value)','ok (done 0#u32)'),('def aspis_core.field.M31.inv','def changed')]
    for before,after in mutations:
        mutated=text.replace(before,after,1); assert mutated!=text
        try: validate(sources,mutated)
        except (AssertionError,ValueError): pass
        else: raise AssertionError('accepted mutated generated slice')
    rust=field.read_text()
    selected_mul=clean(function(rust,'pub fn mul(self, rhs: M31) -> M31'))
    expected_mul=clean('''
        if self.0 < P && rhs.0 < P {
            let x = (self.0 as u64) * (rhs.0 as u64);
            let s = (x & P as u64) + (x >> 31);
            M31(if s >= P as u64 { (s - P as u64) as u32 } else { s as u32 })
        } else {
            M31(reduce_u64(self.0 as u64 * rhs.0 as u64))
        }
    ''')
    assert selected_mul==expected_mul,'R62 optimized M31 source changed'
    assert clean(function(rust,'fn reduce_u64(x: u64) -> u32'))==clean('''
      let x = (x & P as u64) + (x >> 31u32);
      let x = (x & P as u64) + (x >> 31u32);
      let x = x as u32;
      if x >= P { x - P } else { x }
    ''')
    assert 'pub const P: u32 = 0x7fff_ffff;' in rust
    schedule=audit(rust,chain.read_text())
    return {'generated_pins':PINS,'declarations':8,'byte_identical':True,
      'negative_mutations_rejected':len(mutations),'rust_schedule':schedule,
      'slice_sha256':hashlib.sha256(sliced.read_bytes()).hexdigest(),
      'rust_field_sha256':hashlib.sha256(field.read_bytes()).hexdigest(),
      'selected_M31_is_one_fold_guarded':True,
      'selected_M31_differs_from_generated':True,
      'selected_M31_universal_execution_bridge_proved':False,
      'scope':'pinned generated execution plus structural Rust binding; not a verified extraction compiler'}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    for n in ['stage','slice','field','chain']:p.add_argument('--'+n,type=Path,required=True)
    a=p.parse_args(); print(json.dumps(check(a.stage,a.slice,a.field,a.chain),indent=2))
