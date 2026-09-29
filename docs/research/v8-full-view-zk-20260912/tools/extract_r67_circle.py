#!/usr/bin/env python3
"""Checked extraction of the complete OOD circle-map closure.
Expected work is dependency-free release Rust compilation and translation.
Run only in a bounded, swap-disabled build-host scope.
"""
from pathlib import Path
here = Path(__file__).parent
source = (here / 'extract_r64_field.py').read_text()
for old,new in [
    ("'r64-field-extraction'", "'r67-circle-extraction'"),
    ('crate::inverse_probe','crate::circle_probe'),
    ('R64Field','R67Circle'),
    ("'field.rs','r23_width.rs'", "'field.rs','circle.rs','r23_width.rs'"),
]:
    assert old in source
    source = source.replace(old,new)
exec(compile(source,str(here/'extract_r64_field.py'),'exec'))
