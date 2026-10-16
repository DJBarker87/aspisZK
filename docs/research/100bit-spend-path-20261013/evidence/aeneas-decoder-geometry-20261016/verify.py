#!/usr/bin/env python3
"""Read/hash verification of a private printing-only tool build."""
from pathlib import Path
import hashlib, io, json, tarfile

b = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
a = b / 'geometry-evidence.tar.gz'
assert sha(a.read_bytes()) == '2d6b02c1ebe7a9af172f77d065942f0f9cdae24fba7cbaea7f941e2953046db0'
with tarfile.open(a) as tf:
    files = {m.name: tf.extractfile(m).read() for m in tf if m.isfile()}
assert len(files) == 32
for name, pin in json.loads(files['archive-members.json']).items():
    assert len(files[name]) == pin['bytes'] and sha(files[name]) == pin['sha256'], name
old = files['original/aeneas/src/Translate.ml']
new = files['aeneas/src/Translate.ml']
before = b'  Format.pp_set_margin fmt 80;'
after = b'  Format.pp_set_geometry fmt ~max_indent:1000 ~margin:1024;'
assert old.count(before) == 1 and old.replace(before, after) == new
pins = json.loads(files['source-change.json'])['files']
assert len(pins) == 776
assert [n for n, p in pins.items() if p['before'] != p['after']] == ['aeneas/src/Translate.ml']
archive = files['original/inputs/aeneas-exact-source.tar.gz']
assert sha(archive) == '946d65f31e14d65efdbad996d4f706a612fcc62b2a35331fa9e2d525c596e988'
with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
    source = {m.name: tf.extractfile(m).read() for m in tf if m.isfile()}
for name, pin in pins.items():
    assert sha(source[name]) == pin['before'], name
assert sha(new) == pins['aeneas/src/Translate.ml']['after']
receipt = json.loads(files['aeneas-build-a/receipt.json'])
assert receipt['exit_status'] == 0 and not receipt['ten_minute_review_stop']
assert receipt['limits'] == {'memory.high': '6442450944', 'memory.max': '8589934592', 'memory.swap.max': '0'}
assert receipt['time_reports']['aeneas']['process_swaps'] == 0
assert receipt['last_cgroup_observation']['memory.swap.current'] == '0'
assert sha(files['bin/aeneas']) == receipt['binary_sha256'] == '849dc33c427441499c7364d3d7c6426e2ef48be7f9859ab8456efc859394ebd0'
emission = json.loads(files['decoder/runs/aeneas-geometry-a/receipt.json'])
assert emission['exit_status'] == 0 and emission['swaps'] == 0
assert emission['limits'] == receipt['limits']
assert emission['source_revision'] == '72a288c2cf7745c27d1777159215116c22a63f91'
print('PASS:32 members;776 original source pins; one printing-only source patch; capped tool build and same-LLBC emission. Lean closure is not asserted.')
