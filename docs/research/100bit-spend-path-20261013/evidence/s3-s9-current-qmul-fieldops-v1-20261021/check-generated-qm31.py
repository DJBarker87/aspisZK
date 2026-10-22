#!/usr/bin/env python3
"""Check copied generated declaration bodies against the pinned raw Funs snapshot."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
raw = (ROOT / "raw-generated/Funs.lean").read_text()
adapted = (ROOT / "sources/S3S9GeneratedWideMulQM31V2.lean").read_text()
NAMES = (
    "field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call",
    "field.wide_exact.canonical_qm31",
    "field.wide_exact.WideExact.mul_qm31",
    "wide_mul_qm31",
)

def declaration(text: str, name: str) -> str:
    match = re.search(r"(?m)^def\s+" + re.escape(name) + r"\b", text)
    if not match:
        raise SystemExit(f"missing declaration: {name}")
    starts = [m.start() for m in re.finditer(r"(?m)^def\s+", text[match.end():])]
    end_namespace = re.search(r"(?m)^end AspisR1CurrentWide\s*$", text[match.end():])
    cuts = [match.end() + offset for offset in starts]
    if end_namespace:
        cuts.append(match.end() + end_namespace.start())
    end = min(cuts) if cuts else len(text)
    body = text[match.start():end]
    body = re.sub(r"/\-.*?\-/", "", body, flags=re.S)
    return re.sub(r"\s+", "", body)

for name in NAMES:
    if declaration(raw, name) != declaration(adapted, name):
        raise SystemExit(f"generated declaration mismatch: {name}")
print("PASS: all four copied declaration bodies match the pinned generated Funs snapshot")
