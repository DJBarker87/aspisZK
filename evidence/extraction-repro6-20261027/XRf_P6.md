# Compact byte P6 stage results

All **10/10** new Kani harnesses pass. No timeout, memory kill, failed check,
cap raise, stub or function contract. No timed-out XRe harness is rerun.
The original source function calls are the public pinned dependency's
`compact::expand_values` and `compact::check_values`, not a substitute source.
XRf_reference.rs and XRf_actual.rs retain all six inherited references/excerpts
with names prefixed, preserving the correspondence packet read-only. Current
Kani targets use the public compact functions directly; the private excerpts
are not credited as new verified bodies. Cargo locks and tool/artifact hashes
are retained by the final host audit. Rust/Kani compilation uses opt-level3,
overflow checks enabled, one compiler job; logs show optimized profile.

| Attempt | Exact bounded claim |
|---|---|
| K001 | Arbitrary16-byte input,32-byte output: full Result and every arbitrary output index equal inherited safe reference. |
| K002 | Expand16 bytes into a32-byte subslice of a48-byte destination, preserving both8-byte frames and checking every arbitrary destination index. |
| K003 | Input length0..33 with nonzero residue mod16; destination length0..66: Length error and every original destination byte retained. |
| K004 | Aligned input length0..32; destination length0..65 unequal to twice input length: Length error and byte frame. |
| K005 | check_values on32 bytes equals first16-byte check followed by the second only on success; same NonCanonical result. |
| K006 | Same short-circuit decomposition on47 bytes, including15-byte ignored tail. |
| K007 | One16-byte chunk succeeds iff all four arbitrary little-endian u32 limbs are below2147483647. |
| K008 | On48 bytes, failure of the first16-byte chunk implies whole check failure. |
| K009 | For lengths32..47, the incomplete final chunk does not affect check_values. |
| K010 | Expanding32 bytes to64 equals two16-to32 calls, with full successful Results and equality at every arbitrary output index. |

Exact checks, wall/RSS/swap and receipt paths: XRf_KaniSummary.json. Full commands,
source hashes/snapshots, dependency release pin, revisions, optimized settings,
raw logs and time output are in XRf_K001..K010. The shell launches them serially,
with a fresh recorded reservation before every scope. All admitted, zero retries.
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 throughout.

## Non-vacuity and limits

No canonicality assumption appears in K001, K002, K005–K007 or K010. Arbitrary
indices always have a nonempty range. The remaining domain assumptions have
explicit witnesses: K003 n=1,m=0; K004 n=0,m=1; K008 first four bytes255
(noncanonical little-endian first limb); K009 n=32. All other bytes may be zero.
This is inspection of satisfiable harness domains, not a newly executed cover
suite or an inhabitant of the actual top's joint premises.

No arbitrary-length induction,464/928 caller-sized proof, full borrow/allocator
model, emitted Lean carrier association, whole check_values/expand_values leaf
certificate or complete six-leaf composition is established. The earlier XRe
32/64 reference check and short byte-model theorems are reused as recorded,
not re-proved. Remaining obligations are in XRf_OBLIGATIONS.md; its estimated
2–4 check_values targets and3–6 expand_values targets still require unbounded
composition, source/model and caller binding. Actual top premises removed:0;
ledger deltaT0/P0/G0/C0. No shipped file changed, so no three-ELF rebuild trigger.
