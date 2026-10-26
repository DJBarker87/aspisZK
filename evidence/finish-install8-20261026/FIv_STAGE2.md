# Symbolic native composition folds

FIv_Horner24.value and FIv_Horner4.value prove the actual list-backed reverse iterator loops by list induction, using PreparedMul.value at each reached multiplication. No concrete recurrence evaluation, new heartbeat/depth option, or finite large carrier enumeration occurs.

FIv_HornerAlgebra.reversed/four convert the reverse fold to theta^length*seed plus a low-order recursive polynomial. FIv_CompositionValue.value obtains the SAME prepared multiplier, arrays, copy result and fold calls from the actual composition success, then proves its value is theta^28*copy.residual + theta^4*low(semantic24) + low(poseidon4). Canonicality of the coefficients and copy residual remains explicit in this local theorem. This does not prove their R0P semantic meanings and does not remove L146.

FIv_CompositionOperands.reached additionally exports the SAME selector, Poseidon, semantic_packed and copy calls (including validated withdrawal_amount and SAME h). It adds no input premise. The seven tensor pair meanings and22 fast_dots values remain independent open rows.

Attempts014-018 and020 pass, standard axioms only.019 failed on record equality syntax, corrected in020. Per-attempt receipts record exact targets, source revision/hashes, dependency fingerprints, exits, wall time, peak RSS, swaps, cgroup limits and complete axioms output. Budget20/100 Lean charged,17 compiler starts,0/20 Kani. No timeout/memory kill.
