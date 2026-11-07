# NMN retired shapes

K001: actual064 returning shape with parser UnsafeCell context, common H log, full replies and two arbitrary-index frame reads timed out at90s (exit1,104.573114s wrapper,2227716KiB RSS,swap0). No semantic credit. Source archived by hash in NMN_INPUTS.json. Replacement splits scalar forwarding from byte-frame checks, removing both arbitrary-index buffer reads; no timeout/cap increase. Complete byte-frame obligation remains explicit.

K002: scalar replacement reached a builtin memcmp unwinding assertion at bound17 (exit1,3.728713s,345928KiB,swap0), no semantic verdict. This is array-of-three-pointer/usize comparison lowering. K003 replaces both array equalities with six scalar assertions; no bound/time/cap increase.
