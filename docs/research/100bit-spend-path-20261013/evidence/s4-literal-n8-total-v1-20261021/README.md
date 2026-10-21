# Literal N8 reducer totality

This focused owner proves `literal_eight_total`: for arbitrary eight U64 limbs, eight checked reads followed by the selected current M31 reducer succeed. It also proves `literal_eight_success_same_p6_output`, so a successful P6 N8 model on the same input and reducer has exactly the literal sequence output.

The proof uses exact-array read bounds and the accepted `current_wrapper_mod` result. It does not establish the Rust standard-library `from_fn` correspondence or full helper/source caller refinement. The M31 reducer slot is concretely selected; other `Ops` slots are unused here.

Recheck with `python3 check_packet.py`. The Lean object is intentionally excluded; its SHA and selected warm-cache path are recorded in the manifest and command evidence.
