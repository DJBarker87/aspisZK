# NET continuation plan

Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. NEO baseline 62ab0a9cc5; 54/78 functions, 124/257 edges; both Q roots OPEN.

1. Adopted z(2) fixed-backend CM inverse, then QM try_inv/inv; matched controls.
2. Actual complete native windows and caller joins.
3. Import committed NEI arithmetic with provenance, then query_values/query_loop.
4. Nonempty QueryGeometry::for_range.

Budgets: 100 Kani, 80 Lean, 10 extraction. Only actual submitted prover launches count. One capped scope at a time (within granted maximum two). Never launch without reservation exit 0 and allowed:true. Reuse NEO validation, adding checks only. No production changes; all harness instrumentation lives in private host scratch, committed as patches and exact inputs.

Native contract semantic transport remains option-A P6/D188 reclassification. Root PacketDomain, PhysicalInterpretation and runtime trust remain. No 100-bit conclusion is established.
