# Mathematical output and exact wide serialization

Checked `ProverRw21ProofOutput.reference_proof`: for typed mathematical
transcript data, the independent reference proof is exactly the explicit node
result. Both byte-length guards are discharged symbolically, and node errors
are preserved. `ProverRw21ModelBytes.instance_bytes` connects that raw result
to the stable `R1Z.ProverRw21ModelInstance`, through small packing lemmas.
This replaced a recursion-depth failure without changing any recursion,
heartbeat, memory, or swap limit.

Checked `ProverRw21FlatSourceLaw.exact`: the retained extracted P6 wide-byte
serializer returns the exact ordered concatenation of its eight u32 words'
little-endian bytes, for every full-width input. This is stronger than the
previous totality result and has no success/canonicality premise. Generated
proof steps use named symbolic read lemmas; decisions are only on bounds
0..7 and 0..3. Generator preflight is `flat-source-law.py --check`.

Checked byte-carrier round trips, canonical wide-carrier round trips and
injectivity, caller foundation shape decoding, and mathematical trace-column
construction. These do not supply the deployed masking/commitment/oracle
schedule or actual caller byte equations.

Checked `ProverRw21CallerCriterion.criterion` consumes the original rw18
criterion and audit transport. Remaining named assumptions are exactly
P_source_p6, the state reservation equation, and the proof-byte equation.
The latter is not proved for transfer, withdrawal, or general admitted inputs.

The driver in `ProverRw21ProtocolRun` instantiates the honest mathematical
payload on the quartic execution-value carrier. Association/transport to the
privacy endpoint's wide-field model is NOT claimed. Its roots, openings and
node results remain mathematical data; deriving them and the payload from
the deployed caller's inputs remains open. The published serialization
instance therefore is not the requested concrete whole-caller construction.

V164 remains {P_source_p6}; V163 remains OPEN. No headline or deployment
premise is removed. Native gates 1, 9, 10 timed out; gate 2 (arity zero)
passed, with memory/unwinding checks and no stubs. One accidental scheduling
overlap is retained in SCHEDULING-EXCEPTION.md.
