#!/usr/bin/env python3
from pathlib import Path
import hashlib,re,subprocess,sys
packet=Path(__file__).resolve().parents[2]
repo=Path(__file__).resolve().parents[7]
base=repo/"docs/research/100bit-spend-path-20261013"
v10=base/"lean-candidates/s4-minimal-fixed-calls-v10-20261021/extraction/evidence/generated/AspisR1FastDotsMinimalFixedCallsV10/Funs.lean"
v6=base/"lean-candidates/s4-four-dots-fixed-call-v2/sources/FourDotsFixedV6-Funs.lean"
def body(p,n):
 t=p.read_text();m=re.search(r"^def "+re.escape(n)+r"\n.*?\n  := do\n(.*?)(?=^/--|^end |\Z)",t,re.M|re.S)
 assert m,(n,p)
 return m.group(1).rstrip()
for n in ["fast_dots.four_dots_one_loop0_loop0.body","fast_dots.four_dots_one_loop0_loop0","fast_dots.four_dots_one_loop0.body","fast_dots.four_dots_one_loop0","fast_dots.four_dots_one"]:
 assert body(v10,n)==body(v6,n), f"v10/v6 helper body mismatch: {n}"
subprocess.run([sys.executable,str(base/"lean-candidates/s4-minimal-fixed-calls-v10-20261021/extraction/check-extraction.py")],check=True,cwd=repo)
subprocess.run([sys.executable,str(base/"lean-candidates/s4-four-dots-fixed-call-v2/check_adapter.py")],check=True,cwd=repo)
print("PASS: all five generated v10 helper declarations equal their v6 emitted bodies")
print("PASS: v10 extraction receipt/body checker and v6 generated-to-Ops exact adapter checker")
print("Scope: source transformation and pinning only; raw external Funs semantics and Rust/P6 std correspondence remain open.")
