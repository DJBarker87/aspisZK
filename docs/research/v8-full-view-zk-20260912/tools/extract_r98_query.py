#!/usr/bin/env python3
"""Extract R98's actual query entry and explicit source guard, no ctpop model."""
from pathlib import Path
source=Path(__file__).with_name('extract_r72_sampler.py').read_text()
replacements={
"stage=root/'aspis-r20-r69-explicit-20260929-b'":"stage=root/'aspis-r20-r98-query-20260930-b'",
"bc92dd5675b58ba3076b999429f7cbdfc6675baf":"da1110c9f49179292d332e1d300f618ba2d8f5d4",
"sampler_probe":"query_probe",
"-> Result<circle::SecureCirclePoint, transcript::CirclePointSampleError> {\n    t.challenge_secure_circle_point()":"-> Result<alloc::vec::Vec<u32>, transcript::QuerySampleError> {\n    t.challenge_queries_without_replacement(22, 1 << 18, 64)",
"R72Sampler":"R98Query",
}
for old,new in replacements.items():
    assert old in source,old;source=source.replace(old,new)
source=source.replace("manifest=json.loads((stage/'r18-stage.json').read_text())", """manifest=json.loads((stage/'r18-stage.json').read_text())
assert manifest['r98_query']['control_manifest_sha256']=='17ab8a660db4eca296609b6b38028a30537069c45f93ad5afa88d0d8c757d808'
old=(Path(manifest['r98_query']['control'])/'crates/aspis-core/src/transcript.rs').read_text()
assert (stage/'crates/aspis-core/src/transcript.rs').read_text()==old.replace(
 '        if !bound.is_power_of_two() {','        if bound == 0 || (bound & (bound - 1)) != 0 {')""")
exec(compile(source,str(Path(__file__).with_name('extract_r72_sampler.py')),'exec'))
