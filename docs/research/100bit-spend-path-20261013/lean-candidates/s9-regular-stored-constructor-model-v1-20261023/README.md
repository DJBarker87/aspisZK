# Same regular stored value and literal source row mapping

The accepted actual regular driver now supplies its canonical storedValue and exact constructor-factor expression. Both scalar values come from SAME row reads and actual powers/scalar calls; the dot value comes from SAME tensor and actual field operands; both source multiplies and final write remain in its Execution witness. No separate callee output or desired tensor value is assumed. Existing source caller/constructor/powers guards remain explicit for their concrete producer to supply.

Root scalar-constructor semantics is reused. Generic variable-only decoder alias transport plus Eq.trans/congrArg₂ avoids normalizing compound concrete field expressions. The exact source quarter remains in factorPolynomial; inverse4 conversion is separate pending work.

The companion row-index proof uses actual wrapping subtraction under its proved non-underflow condition, keeping word size opaque. Its five literal source kinds map exactly to five constructor rows. Both focused targets passed the first actual check, standard axioms and zero swap.5733selected owner hashes matched for stored-value integration, with only missing project artifacts staged. No runtime source/artifact changes, cold build or full release replay.
