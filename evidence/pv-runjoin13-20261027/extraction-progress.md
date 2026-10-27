# Extraction progress

Gate (a) passed before extraction. Shipped source SHA-256:
b45b6f97c27c891022475a4b5cf7c13b2c3efcd333f3281cb26ce44bad31d629.

Charon 01: preflight has_errors=false; root implementation body present.
21 function declarations. The remaining FnOnce dependencies in this LLBC
are under the unchanged raw helper, which itself calls core::array::from_fn.
The authorized records rewrite has removed its four closure sites; this
first extraction does not establish a concrete R_shipped.
Aeneas 01 exits 2 at FunsAnalysis.ml:134, core/ops/function.rs:250.
The unchanged pinned tools and exact commands/hashes are in the receipts.

Charon 02 admission refused at 2026-10-27T10:07:11 UTC: existing reservation
59,995,324,416 bytes, requested 8,589,934,592, safe limit 59,055,800,320.
No scope launched and no Lean or Kani budget charged. Required three-minute
wait applies before retry. Opaque raw is an isolation experiment; it cannot
by itself establish a fully identified shipped dictionary.

Charon 02 subsequently admitted after the three-minute wait; preflight clean,
5 declarations (records implemented; pair_empty_roots/raw opaque; ZERO8
implemented; core precondition_check opaque). Aeneas 02 strict-joins exits 2
at records line 230 / InterpAbs.ml:1955 while joining the selected-second
borrow contexts. No generated extraction was accepted or installed.
Aeneas 03 without strict-joins was refused at 10:11:53 UTC, reservation
51,405,389,824 + 8,589,934,592 > 59,055,800,320 bytes. Wait three minutes.
