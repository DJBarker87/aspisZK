# FS2 abstract protocol and message-view API inventory

This note records current Lean interfaces relevant to a typed-message protocol view. It describes signatures and existing representation helpers only.

## Generic FS2 layer

In [`FS2/Statement.lean`](../../v8-fs-generic-20261006/lean/FS2/Statement.lean), `FS2.Protocol X M C W Pf I A` has fields `r : Nat`, `msg : Pf → Nat → M`, `samp : Nat → Prefix X M C → M → Sampler I A C`, `decode : I → Table I A → Option (Sampler I A (Prefix X M C × M × C))`, and `extract : X → Table I A → Option W` (lines 94–99). `Sampler` contains `done`, `ask`, and `multi`; neither API contains message `enc`, `dec`, or `decEnc` fields.

`RoundByRound' X M C I A` consists of a table/prefix predicate `doomed` and an error function `ε` (lines 161–164). `D1` is the initial doomed-state condition after extractor failure (171–172); `D2` bounds the generic sampler's extension mass for each typed message `m : M` (177–181); `D3` says a doomed final transcript is rejected (198–201). These definitions operate on `M` and sampler programs, without a byte representation requirement.

## Concrete duplex codec layer

[`FS2/Duplex.lean`](../../v8-fs-generic-20261006/lean/FS2/Duplex.lean) defines `FS2.Duplex.Params M Cv L` with `enc : M → Bytes`, `encLen`, `dec : Bytes → Option M`, and `decEnc : ∀ m, dec (enc m) = some m`, in addition to labels, challenge mapping, initial state, and round count (61–72). The duplex sampler absorbs `enc m`. `decEnc` entails injectivity of `enc` by applying `dec` to an equality of encoded values; this is a property of a particular `Params`, not a field of generic `Protocol`.

[`FS2/DuplexDecode.lean`](../../v8-fs-generic-20261006/lean/FS2/DuplexDecode.lean) constructs a generic `FS2.Protocol` from those parameters (246–253), supplying the duplex sampler and byte-parsing decoder. Concrete decoder proofs use `p.decEnc` to show an encoded message is recovered from its absorb frame; for example, `DuplexDecodes.lean:214` rewrites by `p.decEnc`.

## Existing typed and enriched views

[`TranscriptView.lean`](../lean/TranscriptView.lean) defines an enriched message type with `initial c1` and `payload m`, and an enriched challenge type with ordinary challenges and query results (lines 11–40). `ordinary`, `later`, and `withQuery` transform an already typed list of duplex rounds. The module comment explicitly leaves the connection from actual row-zero bytes to the initial payload outside its proofs.

[`UnifiedProtocol.lean`](../lean/UnifiedProtocol.lean) instantiates FS2 using that enriched message type and the unified sampler (24–32). Its `decode` field is set to `none`; its listed results identify transcript, chain, challenge, and read behavior, rather than supplying a byte decoder or word projection.

[`SemanticPayloadView.lean`](../lean/SemanticPayloadView.lean) maps typed payload constructors to `SemMsgZ` using `toMessage (recoverC2 : State → InitialWord × InitialWord)` (19–24). The C2 representation is an explicit callback argument. `SelectedSemanticMessages.toSemantic` likewise consumes a `recoverC2` callback. These are typed representation maps, not parsers from absorb bytes.

[`SelectedTranscriptParams.lean`](../lean/SelectedTranscriptParams.lean) uses bounded raw bytes as its message carrier, `{ bs : Bytes // bs.length ≤ D }`, with identity encoding and a length-only decoder (20–27). This codec proves the abstract `decEnc` condition for that bounded-byte carrier; it does not by itself enforce row-specific validity or map bytes to literal semantic words.

The older [`R0FS/Protocol.lean`](../../v8-r0-fs-20261006/lean/R0FS/Protocol.lean) and [`R0S/SemStatement.lean`](../../v8-r0-sem-20261007/lean/R0S/SemStatement.lean) provide typed message/challenge constructors for their respective models. This inventory records those interfaces, not a byte-to-word source refinement.
