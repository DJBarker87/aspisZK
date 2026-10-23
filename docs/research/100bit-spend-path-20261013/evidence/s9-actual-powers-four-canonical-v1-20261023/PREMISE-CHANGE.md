# Premises and conclusion

Before: the helper interface required pointwise canonical reads of externally supplied powers arrays `ap0` and `ap1`. Existing S3 powers proofs covered an older FnMut implementation; they did not directly prove this indexed producer.

Now: `actual_powers_four_native_reads_canonical x out hx hrun` quantifies the actual source Wide carrier and exact output array. It assumes only canonical coordinates of `x` and success of the same actual `weights.powers 4 x` call. It derives every successful native output read canonical. The array's mutable writes, initial ZERO/ONE, each successful running-product multiplication, wrapping successor bound, loop decrease and final early return are proved. The intermediate `hmul`, `hzero`, `hone` contracts do not remain in the final theorem.

The multiplier map preserves full Result behavior under canonical inputs; it is not merely acceptance equivalence. No allocation premise enters the pure powers function. The existing model's allocation interface and typed wrapping/source compatibility ports remain explicit producer boundaries.

This is a genuine producer-contract discharge for an array actually returned by the given successful powers call, not an unconditional fact about arbitrary helper arrays. Whole Pair reachability, actual alpha canonicality and helper output canonicality are not conclusions of this packet. No private nominal-carrier equality, oracle law, cost bound or release theorem is introduced.
