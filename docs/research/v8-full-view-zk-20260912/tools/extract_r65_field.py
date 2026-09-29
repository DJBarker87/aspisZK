#!/usr/bin/env python3
"""Reuse the overflow-checked R64 extraction recipe for the CM31 closure.
Run in a bounded, swap-disabled NUC scope. Expected work is dependency-free
Rust compilation and MIR/Lean translation, not elimination or proof generation.
"""
from pathlib import Path
here = Path(__file__).parent
source = (here / 'extract_r64_field.py').read_text()
for old, new in [
    ("'r64-field-extraction'", "'r65-field-extraction'"),
    ('crate::inverse_probe', 'crate::complex_inverse_probe'),
    ('R64Field', 'R65Field'),
]:
    assert old in source
    source = source.replace(old, new)
exec(compile(source, str(here / 'extract_r64_field.py'), 'exec'))
