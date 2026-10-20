#!/usr/bin/env python3
"""Check that the compiled reader cut is raw generated code plus only its validator parameter."""
from pathlib import Path
import hashlib
import sys

ROOT = Path(__file__).resolve().parent
RAW = ROOT / "stage2-resume-query-array-unrolled-reader-opaque-validator-v1-20261020/generated/AspisR1Stage2AdoptedResume/Funs.lean"
COMPILED = ROOT / "stage2-query-reader-success-lean-v13-cursor-20261020/sources/AspisR1Stage2AdoptedResume/Funs.lean"

def reader_decl(path: Path) -> str:
    source = path.read_text()
    begin = source.index("def verifier.resume_read_queries\n")
    end = source.index("\nend AspisR1Stage2AdoptedResume", begin)
    return source[begin:end].rstrip() + "\n"

raw = reader_decl(RAW)
adapted = reader_decl(COMPILED)
adapted = adapted.replace(
    "def verifier.resume_read_queries\n"
    "  (validate_queries : (Array Std.U32 22#usize) → Result (core.result.Result (Array Std.U32 22#usize) verifier.Error))\n"
    "  (bytes : Slice Std.U8) (at1 : Std.Usize) :",
    "def verifier.resume_read_queries\n"
    "  (bytes : Slice Std.U8) (at1 : Std.Usize) :",
    1,
)
adapted = adapted.replace("    validate_queries\n", "    verifier.validate_queries\n", 1)
if raw != adapted:
    print("FAIL: more than the validator-parameter substitution changed the reader declaration", file=sys.stderr)
    sys.exit(1)
print("PASS: exact reader declaration after reverting the parameter/callee substitution")
print("raw reader declaration sha256:", hashlib.sha256(raw.encode()).hexdigest())
print("compiled reader source sha256:", hashlib.sha256(COMPILED.read_bytes()).hexdigest())
