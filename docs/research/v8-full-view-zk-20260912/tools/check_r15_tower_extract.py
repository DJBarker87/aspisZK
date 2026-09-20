#!/usr/bin/env python3
"""Fail closed if the slim field declarations differ from the retained proof."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parents[4]
original = root / 'AspisFormal/AspisFormal/V5ComponentCQM31TowerExact.lean'
slim = Path(__file__).resolve().parents[1] / 'lean/AspisV8R15/ExactTowerBase.lean'
assert hashlib.sha256(original.read_bytes()).hexdigest() == '75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5'
start = 'abbrev P : Nat := 2147483647'
end = 'abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0'

def declarations(path):
    text = path.read_text()
    return text[text.index(start):text.index(end) + len(end)]

assert declarations(original) == declarations(slim)
print('PASS: exact retained tower declarations and certificates; imports/namespace only differ')
