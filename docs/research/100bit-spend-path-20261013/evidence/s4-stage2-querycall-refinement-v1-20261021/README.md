# Stage2 query-call refinement

`query_loop_ten_success_refines` and `query_loop_twelve_success_refines` transport a successful inner-`Ok` Stage2 query loop from call `f` to call `g`, preserving the exact terminal accumulator and batched weights. The only pointwise refinement premise is that every successful `f` call on the same input produces the identical successful `g` call. The source call's counter-advance property is retained to derive the existing symbolic loop chain; no `g` counter-advance premise or literal step unrolling is used.

The proof reuses the accepted ten/twelve chain extractors, maps their `Chain` constructors pointwise, and reconstructs successful loop execution from that chain. This is a model-level loop transport theorem; it makes no Rust runtime or source-adoption claim.

Validation: `python3 check_packet.py`. No compiled object is included.
