# R332 prefix initialization selectors

Uncompiled Lean plumbing draft. It imports the actual R329 initialization theorem, R326 prefix product selectors, and R317 `Slice.last` theorem. The exact selected fragment output equation and specified nonempty/canonical input-read premises remain explicit. It proves the output length, each indexed prefix value, the final output value, a combined initialization bundle, and the selected fragment's actual `Slice.last` result through R317.

The draft does not establish the premises for a caller, prove preceding full-batch guards, address the inverse path, or claim Rust/Std correspondence. Five `#print axioms` commands are included but have not been run. No compile or test was run; lead review is pending.
