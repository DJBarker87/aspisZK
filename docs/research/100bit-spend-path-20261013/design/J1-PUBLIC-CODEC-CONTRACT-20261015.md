# Lead-fixed public-codec contract

The current R1 entrypoint first decodes the 1880-byte ASF8 statement and maps
its payment and lane-transition fields into the borrowed Rust `r0::Public`.
The semantic verifier then serializes that projection using the section-9
`Public::public_bytes` layout. These are two different byte representations.
The checkpoint binds the original public bytes; the semantic transcript uses
the projection. Neither representation may be substituted for the other in a
refinement theorem.

The immediate model is `SemanticPublicWire`. Its `Common` record contains
exactly the shared fields of `R0P.Public`, with an index in `Fin (2^64)`.
`Wire.transfer` supplies a recipient digest; `Wire.withdrawal` supplies an
M31 amount. `toPublic` sets the corresponding variant and options explicitly.
All digests have eight canonical M31 coordinates, and each frontier has 20
digests. The index encoding is eight little-endian bytes, assembled from the
already retained 32-bit codec. No index reduction modulo M31 is allowed.

The serializer follows the inspected source order, including both option
flags. Transfer encoding has 1455 bytes; withdrawal has 1427. The decoder
uses the existing exact canonical field decoder, checks the fixed variant
and option tags, and rejects trailing bytes. `parsePublic` additionally runs
the existing canonical-option checker. Its nonzero withdrawal check is a
semantic shape condition, not a property of `public_bytes` alone.

Checked model lemmas, without source-equivalence assumptions:

- Raw decoding of an encoded `Wire` returns that wire.
- Successful raw decoding determines every input byte by re-encoding.
- `toPublic` is injective and preserves the full bounded index.
- Parsing an encoded canonical wire returns its `R0P.Public` value.
- Successful `parsePublic` yields canonical option shape and a bounded index.

`SemanticPublicCodecComplete` additionally proves that canonical option shape
and an index below `2^64` are exactly the public carrier's parsing conditions:
every such public value has one unique accepted byte list. The exact lengths
above discharge the u32 public-length bound and give initialization-frame
lengths of 1530 and 1502 under the existing P3 frame model. These are focused
NUC results with standard-only axiom audits; see the dedicated
`lean-semantic-public-*` evidence bundles and the lead checksum/source audit.

The model intentionally separates parsing from the terminal's further
validation. A decoded M31 withdrawal amount can exceed the circuit's 30-bit
value range; the Rust terminal rejects such an amount, and the checked spend
relation's bounded output witness cannot satisfy its withdrawal equation.
The parser theorem must not be described as an equivalence to all Rust
terminal guards. The source-to-model direction must preserve those guards
when it derives the production and append premises.

The next source obligations are the ASF8/payment/late decoder's exact
projection into this carrier; correspondence of the Rust serializer to
`encode`; all omitted account fields' bindings; and the tx1/checkpoint/tx2
use of the same immutable public and proof bytes. Pool/domain/sequence,
source current root, and withdrawal destination are not silently added to
the section-9 transcript. Their validation and account binding remain
explicit obligations of the accepted source scope.

This contract fixes the checked model and the next source proof targets. It does not
declare J1 complete, identify an extracted Rust function with the model, or
close any protocol, Fiat–Shamir, knowledge, or privacy gate.
