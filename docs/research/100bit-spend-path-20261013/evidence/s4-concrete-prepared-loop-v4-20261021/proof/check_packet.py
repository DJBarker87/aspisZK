#!/usr/bin/env python3
from pathlib import Path
import hashlib, sys
HERE=Path(__file__).resolve(); ROOT=next(p for p in HERE.parents if (p/"Cargo.toml").is_file())
base=HERE.parents[1]
checks={
 "caller source":(base/"sources/S4Tx1CallerLoopConcreteV4.lean","9a1a41e8dc5c71e0b30d2698553e6b328ea126db64d90c88ff6ec38adae8a8b1"),
 "prepared source":(base/"sources/S4Tx1PreparedLoopConcreteV4.lean","d5b5e3ddfebacfb1fc8e09399ea070251015ed0ef42105ceb2f1128c68574f07"),
 "V4 constructor source":(ROOT/"lean-candidates/s4-accumulator-new-v2-20261021/AccumulatorNewConcreteChildrenV4.lean","f12c26d236ca76b3e7e47497234117ea5244387c07f936dd60420c67cfc5814a"),
}
for label,(path,want) in checks.items():
 if not path.is_file(): sys.exit(f"missing {label}: {path}")
 got=hashlib.sha256(path.read_bytes()).hexdigest()
 if got!=want: sys.exit(f"SHA mismatch {label}: {got}")
caller=checks["caller source"][0].read_text(); prep=checks["prepared source"][0].read_text()
for token in ("withConcreteConstructorChildren ops filled","split := 10#usize","tx1_success_requires_split","tx1_success_same_query_initial_next_zero"):
 if token not in caller: sys.exit(f"missing caller token: {token}")
for token in ("source_caller_reaches_ten_loop","hscanBinding","hprepareBinding","ClaimCanonical gamma","a.next = 0#usize"):
 if token not in prep: sys.exit(f"missing prepared-loop token: {token}")
print("PASS: V4 caller builder, split-10 path, and same-witness prepared-loop source pins")
print("LIMIT: checker does not establish extraction semantics or the explicit upstream prepare/scanner bindings")
