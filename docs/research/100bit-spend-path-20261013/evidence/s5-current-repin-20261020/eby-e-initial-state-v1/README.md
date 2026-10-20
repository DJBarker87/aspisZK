# EbyEDot initial count and accumulator invariant

This module copies the selected emitted Dot.new and EbyEDot.new constructor bodies, with only the inner Dot constructor call renamed to the copied sourceDotNew. The checker verifies both copies against the pinned generated Funs source. On successful EbyEDot construction, Lean proves count.val = 0 and all four accumulator arrays satisfy the zero-count sumsBelowCount invariant.

The theorem is standard-axiom-only. It supplies the initializer for the four-Dot count-step induction; it does not prove an enclosing Rust caller or the full EbyE product.
