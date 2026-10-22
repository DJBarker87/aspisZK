#!/usr/bin/env python3
"""Hash and exact emitted-body cut checker for the V10 head-loop packet."""
import hashlib, json, pathlib, re
ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO = ROOT.parents[4]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def fail(msg): print('FAIL:', msg); raise SystemExit(1)
manifest=json.loads((ROOT/'manifest.json').read_text())
for mod in manifest['modules']:
    p=ROOT/mod['source']
    if not p.is_file() or sha(p)!=mod['source_sha256']: fail('module source pin mismatch: '+str(p))
for name,pin in manifest['direct_import_source_map'].items():
    p=(pathlib.Path(pin['source']) if pathlib.Path(pin['source']).is_absolute() else (ROOT/pin['source'] if (ROOT/pin['source']).exists() else REPO/pin['source']))
    if not p.is_file() or sha(p)!=pin['source_sha256']: fail('source owner pin mismatch: '+name+' '+str(p))
generated=(ROOT/'dependencies/AspisR1FastDotsMinimalFixedCallsV10-Funs.lean').read_text()
adapted=(ROOT/'sources/S4V10HeadLoopBoundV1.lean').read_text()
def body(text, marker, next_marker):
    a=text.index(marker); b=text.index(next_marker,a); block=text[a:b]
    return block[block.index(':= do')+len(':= do'):].strip()
gen=body(generated,'def fast_dots.four_dots_one_loop0.body','/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop 0:')
actual=body(adapted,'def v10HeadBody','\ndef v10HeadLoop')
needle='fast_dots.four_dots_one_loop0_loop0 { start, «end» := i1 } q g slot\n        sums'
replacement='v10TermLoop (adaptOps ops) { start, «end» := i1 } q g slot sums'
if gen.count(needle)!=1: fail('generated nested-loop call cut not unique')
gen=gen.replace(needle,replacement)
def toks(s): return re.findall(r'[A-Za-z_][A-Za-z0-9_\.]*|[0-9]+#(?:usize|u64|i32)|[^\s]',s)
if toks(gen)!=toks(actual):
    for i,(x,y) in enumerate(zip(toks(gen),toks(actual))):
        if x!=y: fail(f'body token mismatch at {i}: emitted={x!r} adapter={y!r}')
    fail(f'body token count differs emitted={len(toks(gen))} adapter={len(toks(actual))}')
print('PASS: packet source hashes, exact generated V10 head-body cut, and one nested term-loop adapter replacement')
