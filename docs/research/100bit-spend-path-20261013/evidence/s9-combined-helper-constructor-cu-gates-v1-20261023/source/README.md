# S9 helper 933 + constructor v2 combined candidate

This immutable source candidate starts from the exact 9338607a S9 helper candidate (`attempt2/candidate/src/weights.rs`) and applies only the already-gated constructor v2 frame split: calculate initialized locals, then call out-of-line `Weights::box_from_parts`. The factored S2 helper declaration and all other source bytes are preserved. It is an isolated candidate; it is not adopted into production.

The constructor path changes allocation-failure semantics: the original fallible allocation could return `Error::Allocation`; `Box::new` failure aborts. This must remain explicit in any later refinement claim. The standalone constructor stack result does not substitute for a stack audit of this combined candidate.
