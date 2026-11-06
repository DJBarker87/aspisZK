# NLF pinned SDK / std correspondence

Target not yet established. Ruling (be)(2) replaces NJN's failed guard-drop
extraction requirement with a transcription over the existing std interpretation.
No extraction is run. This is option-A P6/D188 trust reclassification, not removal.
Each row below is a ReviewedTranscription item; no new runtime trust row.

All line numbers refer to the archived, sha256-addressed inputs listed in
NLF_SDK_PINS.json. Source versions must not be inferred from a compatible semver:
the FROZEN Cargo.lock is used. solana-program 2.3.0 reexports AccountInfo from
solana-account-info 2.3.0; ProgramError is solana-program-error 2.2.2.

| Item | Exact source steps | Lean transcription / interpretation |
|---|---|---|
| NLF-RT-shared-data | account-info lib.rs 121 signature; 122 self.data; 123 try_borrow; 124 map_err AccountBorrowFailed; 125 return | NLF_SdkModel.try_borrow_data selects SAME accounts[a].data, wrap .shared, exact ProgramError.accountBorrowFailed, no token on Err |
| NLF-RT-exclusive-data | 127 signature; 128 self.data; 129 try_borrow_mut; 130 same map_err; 131 return | try_borrow_mut_data / wrap .exclusive; no substitution of RefMut-returning contracts |
| NLF-RT-shared-lamports | 109 signature; 110 self.lamports; 111 try_borrow; 112 map_err; 113 return | try_borrow_lamports selects accounts[a].lamports |
| NLF-RT-exclusive-lamports | 115 signature; 116 self.lamports; 117 try_borrow_mut; 118 map_err; 119 return | try_borrow_mut_lamports, distinct admitted data/lamport cells |
| NLF-RT-try-data-len | 97 signature; 98 try_borrow_data()?; deref slice len; temporary guard destroyed before return; 99 end | try_data_len / scalar / release, complete Result and counter restoration |
| NLF-RT-data-len | 93 signature; 94 self.data.borrow().len(); temporary destroyed; 95 end | data_len: successful scalar result, conflict abort is none. Borrow panics; it must NEVER be silently mapped to a returned SDK Err |
| NLF-RT-try-lamports | 76 signature; 77 try_borrow_lamports()?; double deref; Ok scalar; 78 end | try_lamports uses scalar with Payload.money (u64 interpreted as Nat); drop before return |
| NLF-RT-lamports | 72 signature; 73 self.lamports.borrow(); double deref; drop; 74 end | lamports: same scalar or abort on conflict |
| NLF-RT-keys-owner | 68 unsigned_key; 69 self.key; 70 end; public key field 24 and owner field 30 | unsigned_key / owner are direct projections, full List UInt8 key/owner values; no hash/value oracle |
| NLF-RT-data-field | public data Rc field 28, lamports Rc field 26 | Account.data / lamports are CELL identities, not independent copied payloads. Runtime admission installs actual identities; no SDK method named data or owner exists here |

The RefCell representation is std interpretation under (au)/(be), not a proof of
Rust unsafe internals. Its domain excludes Ref clone/map_split/leak, negative
counters from split mutable guards, reallocation, concurrency and re-entrancy.
Existing SDK/Allocator/runtime trust boundaries remain explicit. No integer
address comparison fabricates a typed guard. Native counter reads are observations
of safely constructed cells; every guard is created by the real SDK and dropped
with its actual Rust destructor. On the valid domain flag = -1 for the sole
writer, otherwise the complete shared-token count; shared acquisition requires
count < 2^63-1; exclusive acquisition requires zero.

| Existing std interpretation | Pinned deployed core cell.rs source steps | Lean |
|---|---|---|
| try_borrow | 1013-1035: BorrowRef::new on self.borrow, same value pointer, Ok Ref or Err BorrowError | shared; payload unchanged, shared token added, conflict leaves state unchanged |
| shared counter admission | 1403-1422: wrapping_add(1), reject nonpositive, write positive count | flag/readers length and bound 9223372036854775807; fresh token is GHOST allocation, not an extra SDK admission test |
| try_borrow_mut | 1106-1128: BorrowRefMut::new, same value pointer, Ok RefMut or BorrowMutError | exclusive; only writer-none/readers-empty succeeds |
| exclusive admission | 1806-1817: only UNUSED (=0) changes to UNUSED-1 | exclusive_result / exclusive_counter |
| Ref deref | 1470-1472: self.value.as_ref() | deref SAME cell payload; token unchanged |
| RefMut deref / deref_mut | 1856-1858 / 1865-1867: as_ref / as_mut on SAME value | exclusive_deref and exclusive write frame |
| Ref map | 1515-1520: apply projection to &*orig; MOVE orig.borrow into returned Ref | mapView; same Guard (cell,token,kind), projected value |
| RefMut map | 1660-1666: projection on &mut *orig; MOVE orig.borrow into returned RefMut | mapView identity plus the exclusive write law; no extra writer |
| Ref/RefMut move | ordinary Rust move of guard fields; no clone/drop at move | token identity retained; no new acquisition event |
| Ref drop | guard field BorrowRef::drop, 1428-1432: assert positive, decrement | dropShared erases exactly one live token; second drop invalidToken is outside typed Rust domain |
| RefMut drop | BorrowRefMut::drop, 1797-1801: assert negative, increment | dropExclusive consumes writer, -1 to 0 on unsplit domain |

Payload byte lists use UInt8. The lamport Nat is the interpretation of the typed
u64, with no unbounded arithmetic operation introduced by a getter. Empty-data
getters are additional native probes; the reusable statement's main required
scalar roots are data_len/try_data_len and lamports/try_lamports.

Native configuration is optimized cargo-kani 0.67.0 with deployed verifier
features and its own pinned rustc; it is not the SBF compiler. Pinned deployed
core source is 1.89.0-sbpf-solana-v1.52; the difference is recorded, and the std
semantic interpretation is the existing trust item, not a claimed binary equality.
The source-to-ELF gate is inherited, not reproduced (no shipped change).

NLF_FAILING_STEP records rejected native queues; none is a failing control.
Record contract calibrations, when used, apply only to their exact observation
shape. No Ref/RefMut-returning function is ever stub_verified.

The deployed unsplit-counter range is additionally proved by NLF_BorrowBounds,
then exported as NLF_SdkBorrowLaw.admitted_counter_range. The source-use inventory
NLF_SOURCE_USES.json finds no explicit Ref::map/RefMut::map, Ref clone/map_split/
leak in the frozen verifier/Pool source selections. The map probes and pure
current-payload projection laws are additional reusable support. An effectful
arbitrary RefMut::map closure would need its own effect law; it is not licensed
by a pure projection equality.
