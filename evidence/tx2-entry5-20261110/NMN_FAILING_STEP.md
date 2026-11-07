# NMN retired shapes

K001: actual064 returning shape with parser UnsafeCell context, common H log, full replies and two arbitrary-index frame reads timed out at90s (exit1,104.573114s wrapper,2227716KiB RSS,swap0). No semantic credit. Source archived by hash in NMN_INPUTS.json. Replacement splits scalar forwarding from byte-frame checks, removing both arbitrary-index buffer reads; no timeout/cap increase. Complete byte-frame obligation remains explicit.

K002: scalar replacement reached a builtin memcmp unwinding assertion at bound17 (exit1,3.728713s,345928KiB,swap0), no semantic verdict. This is array-of-three-pointer/usize comparison lowering. K003 replaces both array equalities with six scalar assertions; no bound/time/cap increase.

K027: actual241 validate-Err union over26 ProgramError variants, one-character Borsh payload, empty unread account buffers and Ok slot timed out90s (wrapper145.141174s,3163440KiB,swap0). No semantic/native credit. Replacements split by error variant and independently test Ok(Box<Statement>) construction; no unchanged union replay, timeout/cap increase or claim of full241 coverage.

K028: full typed Box<Statement> constructor experiment FAILS a pointer-offset same-allocation check (52.972478s,2437528KiB,swap0), not a timeout. No parent/allocator credit. The attempted header immediately before Box::new data was not within the allocation Kani gave it. Next isolation compares direct stateless allocator dispatch with Box::new and separately constructs a Box from its valid returned pointer; never infer allocator semantics from this failed experiment.

K035 direct-allocator full nested statement constructor union timed out90s (104.025109s wrapper,3127684KiB,swap0). Retired. Replacement splits PrivateTransfer/Withdrawal and uses all-bit-valid numeric PAYLOAD records after recursive source-field validation; outer enum is always a normal Rust variant. No guard/reference/enum is raw-havocked; no field canonicality assumed; no cap/timeout increase.

K036 numeric-payload PrivateTransfer parent constructor split timed out90s (102.586531s,2989764KiB,swap0). Retired. All future diagnostic parent branches cut unexpected encoder/auth/emit/error suffixes to panic, preventing accidental cryptographic unwinding. Next independent member is the25 non-String ProgramError union; the boxed-success path stays OPEN pending smaller constructor/frame isolation.
