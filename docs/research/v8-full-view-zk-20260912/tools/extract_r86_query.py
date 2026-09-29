#!/usr/bin/env python3
"""Extract the actual bounded q22 source, using the pinned R72 toolchain.

No sampler implementation is replaced by a model. The only Rust source edit
is an appended public entry with the selected count/bound/draw-cap constants.
"""
from pathlib import Path
source=Path(__file__).with_name('extract_r72_sampler.py').read_text()
source=source.replace("p.add_argument('--include-map-err',action='store_true');a=p.parse_args()",
    "p.add_argument('--include-map-err',action='store_true');p.add_argument('--include-power-two',action='store_true');a=p.parse_args()")
source=source.replace("'--start-from','crate::sampler_probe','--include','core::option',",
    "'--start-from','crate::sampler_probe','--include','core::option',*(['--include','core::num::_::is_power_of_two']if a.include_power_two else []),")
replacements={
"stage=root/'aspis-r20-r69-explicit-20260929-b'":"stage=root/'aspis-r20-r85-compose-20260929-a'",
"bc92dd5675b58ba3076b999429f7cbdfc6675baf":"b1a0fdc499fdfa556c4c74cf7e4471bd7a1a15e4",
"sampler_probe":"query_probe",
"-> Result<circle::SecureCirclePoint, transcript::CirclePointSampleError> {\n    t.challenge_secure_circle_point()":"-> Result<alloc::vec::Vec<u32>, transcript::QuerySampleError> {\n    t.challenge_queries_without_replacement(22, 1 << 18, 64)",
"R72Sampler":"R86Query",
}
for old,new in replacements.items():
    assert old in source,old
    source=source.replace(old,new)
source=source.replace("manifest=json.loads((stage/'r18-stage.json').read_text())", """assert sha(stage/'r18-stage.json')=='018879a442490fe9ba4b495be8dbb767254f8f985168660be752b4e917ccafea'
manifest=json.loads((stage/'r18-stage.json').read_text())""")
exec(compile(source,str(Path(__file__).with_name('extract_r72_sampler.py')),'exec'))
