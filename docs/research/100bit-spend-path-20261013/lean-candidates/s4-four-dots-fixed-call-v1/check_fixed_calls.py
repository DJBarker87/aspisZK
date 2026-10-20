#!/usr/bin/env python3
"""Mechanical source/LLBC-emission checker for the v6 fixed-call suffix."""
from pathlib import Path
import hashlib, re, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE if (HERE / 'sources/v6').is_dir() else HERE.parents[1] / 'docs/research/100bit-spend-path-20261013/lean-candidates/s4-four-dots-fixed-call-v1'
src = (ROOT / 'sources/v6/fast_dots.rs').read_text()
funs = (ROOT / 'sources/v6/Funs.lean').read_text()
def sha(b): return hashlib.sha256(b).hexdigest()
expected_source_sha = 'afdf668803e35bcfd0d26b4d8d1adf6bf04205f9c35ed767343f60c49c924952'
expected_funs_sha = '38276aed2316117b0b17d492f2e1e9894de1cce0e8c2db306ddf34bae011c760'
assert sha(src.encode()) == expected_source_sha
assert sha(funs.encode()) == expected_funs_sha

rust = re.search(r'pub fn four_dots_fixed\(q: &\[u8\], g: &\[WideExact; 29\]\) -> \[WideExact; 4\] \{.*?\n\}', src, re.S)
assert rust, 'Rust candidate function not found'
rust_body = rust.group(0)
expected_rust = '''pub fn four_dots_fixed(q: &[u8], g: &[WideExact; 29]) -> [WideExact; 4] {
    let q: &[u8; 608] = q[..608].try_into().unwrap();
    [
        four_dots_one(q, g, 0),
        four_dots_one(q, g, 1),
        four_dots_one(q, g, 2),
        four_dots_one(q, g, 3),
    ]
}'''
assert rust_body == expected_rust, 'Rust body differs from pinned candidate expression'

lean = re.search(r'def fast_dots\.four_dots_fixed\n.*?\n  := do\n(.*?)\n\nend AspisR1FastDotsCurrent', funs, re.S)
assert lean, 'generated Lean definition not found'
lean_body = lean.group(1)
expected_lean = '''  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U8) q { «end» := 608#usize }
  let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
  let q1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let we ← fast_dots.four_dots_one q1 g 0#usize
  let we1 ← fast_dots.four_dots_one q1 g 1#usize
  let we2 ← fast_dots.four_dots_one q1 g 2#usize
  let we3 ← fast_dots.four_dots_one q1 g 3#usize
  ok (Array.make 4#usize [ we, we1, we2, we3 ])'''
assert lean_body == expected_lean, 'generated body differs from pinned expected sequence'
slots_rust = re.findall(r'four_dots_one\(q, g, (\d+)\)', rust_body)
slots_lean = re.findall(r'four_dots_one q1 g (\d+)#usize', lean_body)
assert slots_rust == ['0','1','2','3']
assert slots_lean == ['0','1','2','3']
helper = re.search(r'fn four_dots_one\(.*?\n\}', src, re.S)
assert helper, 'helper function not found'
assert 'array::from_fn' not in helper.group(0)
assert 'Array.make 8#usize [ m, m1, m2, m3, m4, m5, m6, m7 ]' in funs
assert 'from_fn' not in funs, 'generated module unexpectedly retains from_fn'
print('PASS source SHA and generated Funs SHA')
print('PASS fixed-call Rust source body: slice conversion then slots 0,1,2,3')
print('PASS generated Lean body: same prefix call order and Array.make return')
print('PASS helper reduction uses explicit 8 entries; emitted module has no from_fn')
