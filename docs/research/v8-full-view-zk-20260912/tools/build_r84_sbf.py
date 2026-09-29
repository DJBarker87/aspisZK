#!/usr/bin/env python3
"""Reuse the pinned build/export/stack gates for the separately gated profile."""
from pathlib import Path
s=Path(__file__).with_name('build_r20_sbf.py').read_text()
old="assert meta['current_T_unchanged'] or meta.get('basis_profile')=='minimum-support-163'"
assert s.count(old)==1
s=s.replace(old,"assert meta['basis_profile']=='signed-bit-permutation-two-swaps' and len(meta['r84_compact']['affine_gate_logs'])==2")
exec(compile(s,str(Path(__file__).with_name('build_r20_sbf.py')),'exec'))
