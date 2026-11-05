# Native membership split

K001 isolates the missing slice-membership law but times out with variable
prefix length and a reference loop. K002 replaces the reference loop with a
straight disjunction and specializes the domain to length0. Pending outcome.
Each succeeding length-specific candidate must retain all array cells arbitrary,
including unused cells. Scalar x is arbitrary; the caller masks it but no mask
precondition is imposed on membership. Contracts are read-only.

Native stages still required after membership: SAME block/word cursor and
survivor/draw invariant, exact frame, inner/outer loop association, chronological
cuts from the physical caller (including unsuccessful attempted syscall). None
is credited by the reference membership theorem. Any failed or timed-out
contract is excluded from stub_verified use. No Std semantic trust is silently
expanded to the caller conclusion. No extraction retry is authorized.
