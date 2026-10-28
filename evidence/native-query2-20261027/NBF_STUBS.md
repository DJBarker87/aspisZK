# NBF replacement table

No field multiplication is run in Kani. No field-operation stub is introduced.
Inherited field specifications remain in LPh_STUBS.md, unused by K001–K003.

| Stub | Paired Lean theorem | Domain and credit |
|---|---|---|
| NBF_context for update_residue_row | NBB_Row.source; NBB_RowTrace.native_result; NBB_RowWitness.construct | Context-only no-op overapproximation; K002 checks the address, call count, arguments and Vec metadata. It supplies no row-value/frame credit. Actual row domain: U64 row, four power words<P, basis<P, each old word in SAME terms phase. |
| NBF_write for update_residue_row | NBB_Row.source with NBF_Read.push and NBF_Frame.set_frame | Every row reply is havoced; K003 checks one selected-row write on arbitrary 64-row contents and arbitrary observation index/limb. Phase/canonicality are unnecessary for this routing/frame gate; exact values use the inherited row theorem. No final whole-buffer equality is assumed. |

NBF_Read.push derives the actual Vec read and row phase from the SAME list read
and cursor invariant. Canonical power and basis remain explicit upstream
premises: they are not obtained through a stub assumption. This closes the
local selected-row context in its allocated64/capacity64 domain; arbitrary
allocator/capacity lowering remains the inherited TrustedStd/P6 boundary.
The whole query caller installation remains open.
