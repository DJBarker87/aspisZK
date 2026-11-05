# Reference transcription and source cut

IN PROGRESS, no CLOSED claim. NGY_CUT.json pins the frozen verifier body and the exact two-line cut. The generator extracts the two lines, retaining match evaluation and map_err/? unchanged. Its sole inner-cut substitution is the ruled-(y) child call `oracle(&mut dot, g[l], scalar, post, reply, &mut log)` for `dot.push(g[l], scalar)`. Surrounding wrapper materializes full native Dot prestate, captures Parse/control and returns Dot state and local log. This is a SOURCE CUT; it is not an extraction of the whole frozen function. No whole-function equality is assumed.

Rust f_ref correspondence (NGY_native.rs.txt):

- Read scalar by point 0..2 claims, 3 extra, 4 before_z1, 5 decoded y1.c0. Lean uses the existing ClaimScalar.read port, which has the same case split; selected-byte/c0 laws are NGU-owned and reused.
- Read coefficient g[l]. Lean uses the same Array.index_usize port and ePort conversion.
- Log value, scalar, complete before/after states, full Result arm and exactly one call. Lean Entry stores those six items; singleton list is the ordered one-iteration trace.
- Assign arbitrary post sums and count only to Dot. Lean reference returns `after` without restriction; no error-arm rollback is invented.
- On Ok, next=l+1; on Err, Parse and retain l. Lean Control.advance/parse explicitly encode the same distinction. The outer loop's error abort is not a continuation.
- Inputs sem/y1/g are shared and the safe oracle has no reference to them. Lean framed carries the entire input tuple, including unread data, unchanged.

Native log `reply: bool` encodes the exhaustive two inhabited cases of Result<(),()>: true=Ok(()), false=Err(()). The oracle returns that exact Result and the wrapper observes the actual map_err/? result. There are no omitted child error variants.

No products occur in this cut. The child arithmetic belongs to the CLOSED NFG packet and NGU_LPm_PublicPort.source; arithmetic stubs are not reproduced.

Native carrier domain: point<6, lane<29, y1 length928; for point5 only, all eight selected u32 little-endian words<P. This is required by the actual field(...).unwrap, and follows from NGU_LPt_ByteDomain/SelectedDomain on the caller's SAME checked expansion. Other sem matrix limbs and g limbs are arbitrary for native control. Lean child installation additionally establishes their canonicality and count<29 from NGU ReadDomain/Bounded, never by constraining the arbitrary oracle reply.

Verified frame: all public fields are quantified, transcript state/next_row/hash payload are arbitrary. The cut is generic in H and never reads roots/challenges/alpha/state_before_z0/z/transcript/H. Its field-access footprint is syntactically checked by the generator. A generic input value of any H is framed by shared reference and never invoked; the harness concrete Hash(u64) supplies arbitrary payload for its instantiation. The all-H extension relies on the unchanged generic source footprint and P6 Rust reference semantics, not on asserting equality between only the fixed NGU fixture fields.
