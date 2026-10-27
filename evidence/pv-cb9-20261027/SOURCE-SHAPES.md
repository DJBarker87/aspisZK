# Shipped-root shape review

All statements must preserve arbitrary inputs and complete Aeneas Result.

- op226 / V243: `Public::public_bytes` serializes the selected public enum. Nested `fields` iterates M31 references, rejects noncanonical limbs with Error::Public, and appends bytes to an allocated vector. The explicit frontier calls do not eliminate the reference-producing fields iterator.
- op227 / V244: `Public::terminal_qm31` uses `core::array::from_fn` to gather 84 entries using i/28 and i%28, calls terminal_parts, maps its first component, and preserves conversion to Error::Public. No output-only success theorem suffices.
- op228 / V245: registry calls legacy registry and schedule, consumes schedule, uses legacy.iter().find, translates auxiliary tuples and allocates output; CopyLayout failures and vector carrier remain required.
- op230 / V247: helper_sum uses lazy bool.then closure. Incorrect-length slices return None; length1024 uses iter().copied().fold and QM31::add. The arithmetic fold is not suitable for Kani under ruling (k).
- op250 / V257: ordinary_sample invokes low_base_p_digits and decode8. The shared gamma preflight obstruction is in low_base_p_digits (mutable reverse iterator); this root still requires its own exact receipt.
- op251 / V258: materialize returns Result<Vec<WideExact>, Error>; allocating/filling the whole vector and all failure paths must be kept.
- op252 / V259: Weights::new returns Result<Box<Weights>, Error>; the carrier and allocation failures cannot be replaced by unconditional ok.
- op254 / V261: powers is const-generic for arbitrary N. It fills an array with successive WideExact products and has an early return inside the loop. Direct Aeneas prepass refuses the nested-loop-return shape; no theorem claimed.
- op259 / V265: SKIP(sibling), PV_CB_Op259Exact.op259_source already exists on codex/pv-cb-20261026.

No listed root is classified as a purely native-effect op. Allocation is part of the complete Result obligations above; it is not being used to claim a row discharged or silently deferred. Any separate native-effect law belongs to pv-runjoin, including allocator/OOM/ownership semantics not supplied by Aeneas.
