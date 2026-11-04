# Runtime and representation scope

The approved RuntimeReturnData row is retained as named trust. NFO uses it
only at nonempty length792; it does not prove the validator/runtime body.

The pinned solana-cpi2.2.1 SDK getter returns None when the syscall reports
length0, and Some((program_id,buffer[..min(size,1024)].to_vec())) otherwise.
The Pool ELF agrees:0x610b0 branches on zero to0x611c0's None discriminant.
Consequently an interpretation of the approved row that demands Some(P,[])
for an empty set is incompatible with this API. This unused-domain issue is
reported, not silently amended: no empty-byte instance enters NFO's association.
The final joint non-vacuity/runtime-realization gate must use an explicitly
scoped nonempty/792 instance or obtain a lead/owner clarification of the row.
No contract or trust inventory is edited here.

For positive SDK replies, the ELF allocates/copies exactly the selected length
and stores that length in both Vec metadata slots: r7 is the selected size,
capacity is stored at0x611a8 ([r6+0x20]), and the common continuation stores r7
through the +0x30 len slot selected at0x611b0. This supports the exact-capacity
cut's domain on production getter replies. It is STATIC representation evidence;
NFO does not equate it to a checked arbitrary-runtime ABI/carrier refinement.
The full window and source hashes are retained. Both registry source copies
have identical hashes; no registry copy is guessed or modified.

K006 remains the warning against claiming equal pointers for all valid Vec
representations: an arbitrary larger-capacity Vec may shrink on into_boxed_slice.
The KMX one-iteration/value-law route and Box ownership cuts are separate
support, not a new global allocator or SDK trust law. The deployed Pool consumes
the typed value and then re-encodes it; its direct exact_bytes shortcut is OFF.
