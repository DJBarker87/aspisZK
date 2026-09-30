#!/usr/bin/env python3
"""Full record-canonicality checks for new word encoding, plus old controls."""
from pathlib import Path
source=Path(__file__).with_name('check_r19_wire_controls.py').read_text()
source=source.replace('assert len(original) <= 40314','assert len(original) <= 59556')
source=source.replace('head + 621*i + off','head + 640*i + off').replace('[0, 403, 589, 620]','[0, 416, 608, 639]')
source=source.replace("changed('truncated', original[:-1])", """for record in range(22):
    for limb in range(152):
        for invalid in [(1<<31)-1,1<<31,0xffff_ffff]:
            bad=bytearray(original);at=head+640*record+4*limb
            bad[at:at+4]=invalid.to_bytes(4,'little')
            changed(f'word-noncanonical-{record}-{limb}-{invalid}',bad)
changed('truncated', original[:-1])""")
exec(compile(source,str(Path(__file__).with_name('check_r19_wire_controls.py')),'exec'))
