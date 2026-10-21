from pathlib import Path
import hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'fast_dots.rs'
V6=ROOT.parent/'s4-four-dots-fixed-call-v1/sources/v6/fast_dots.rs'
FUNS=V6.with_name('Funs.lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SOURCE)=='53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602'
assert sha(V6)=='afdf668803e35bcfd0d26b4d8d1adf6bf04205f9c35ed767343f60c49c924952'
assert sha(FUNS)=='38276aed2316117b0b17d492f2e1e9894de1cce0e8c2db306ddf34bae011c760'
a=SOURCE.read_text(); b=V6.read_text()
def body(s,name):
 m=re.search(r'pub fn '+name+r'\(q: &\[u8\], g: &\[WideExact; 29\]\) -> \[WideExact; 4\] \{.*?\n\}',s,re.S)
 assert m,name
 return m.group(0)
v10=body(a,'four_dots')
v6=body(b,'four_dots_fixed').replace('four_dots_fixed','four_dots')
assert v10==v6
h10=re.search(r'fn four_dots_one\(.*?\n\}',a,re.S).group(0)
h6=re.search(r'fn four_dots_one\(.*?\n\}',b,re.S).group(0)
assert h10==h6
assert 'from_fn' not in a
lean=re.search(r'def fast_dots\.four_dots_fixed\n.*?\n  := do\n(.*?)\n\nend AspisR1FastDotsCurrent',FUNS.read_text(),re.S).group(1)
assert all(f'fast_dots.four_dots_one q1 g {i}#usize' in lean for i in range(4))
print('PASS v10 entry/helper exactly match accepted v6 fixed-call Rust bodies modulo public function name')
print('PASS pinned v6 emitted Lean body contains four sequential helper calls and Array.make return')
print('Scope: source/body correspondence only; exact v10 Charon/Aeneas replay is independently checked by extraction/check-extraction.py; frozen-Rust equivalence remains open.')
