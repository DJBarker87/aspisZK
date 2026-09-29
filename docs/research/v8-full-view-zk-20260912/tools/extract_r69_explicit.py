#!/usr/bin/env python3
"""Extract the real fixed-arity execution candidate with no source normalization."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'extract_r64_field.py').read_text()
for old,new in [
    ("'r64-field-extraction'", "'r67-circle-extraction'"),
    ("'aspis-r20-r62-gather-20260929-b'", "'aspis-r20-r69-explicit-20260929-b'"),
    ('crate::inverse_probe','crate::circle_probe'),
    ('R64Field','R69Explicit'),
    ("'field.rs','r23_width.rs'", "'field.rs','circle.rs','r23_width.rs'"),
    ("'--dest-file'", "'--include','core::option','--dest-file'"),
]:
    assert old in source
    source=source.replace(old,new)
exec(compile(source,str(here/'extract_r64_field.py'),'exec'))
