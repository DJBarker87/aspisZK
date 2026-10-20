# Exact geometry grouping callback and inverse slot correspondence

PROVED: the unchanged extracted nested FnMut callback from the frozen `map(|i|array::from_fn(|j|flat_inverse[5*i+j])).collect()` expression preserves its captured state and reads precisely flat slot `5*i+j`, deriving both checked scalar operations and the actual Vec read from its success. The retained source expression is unchanged in an explicit-input helper cut.

PROVED: the ordered five-word input records flatten at exactly that slot. Composing the checked geometry-input/batch-inverse candidate with an actual successful callback read gives the individual field inverse of that query's original denominator at slot j. Array order is preserved; no independent prefix/product/flat-inverse success premise is introduced. The existing per-query nonzero guarantee remains explicit.

Five focused NUC targets, three standard-only theorem reports, -M4400 defaults, High1GiB/Max2GiB/Swap0. Charon/Aeneas both passed for the unchanged expression cut, but the generated whole function has three external operation boundaries: core.array.from_fn, Iterator.map.default and Map.next. Their axiom template was NOT compiled. Only byte-exact generated inner callback declarations and Types (resource options removed) were selected for checking. No whole map/from_fn/collect theorem is claimed.

OPEN: concrete stdlib map/from_fn/collect source correspondence, full grouping constructor, original input/prefix iterator equivalence/adoption, actual per-query nonzero backend instance, full frozen caller/runtime identity and complete 100-bit proof. Existing field/algebra/source owners are reused; no full replay, binary artifacts or production edit.
