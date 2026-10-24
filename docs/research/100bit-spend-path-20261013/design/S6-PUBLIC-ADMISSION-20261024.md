# S6 public admission removed from physical byte consumers — 2026-10-24

**Closed named port:** `Port1_ByteDriver.PublicAdmission` for the concrete current
codec/first installation. The original physical-byte accepted transport and
source-driver substitution now have no separate S6 admission premise.
Whole S6, native SDK/source interpretation, frozen2 model order and the actual
100-bit release target remain open. No production source or security metric
changed.

`S6CurrentPublicAdmissionV1.decoded_length` starts from successful
`Port1_Driver.decodeSemantic (install adapter verifier) pub`. It inverts the
SAME decoder call and uses the concrete accepted inverse to derive
`pub.val.length = 1880`. Encoder success, public size and validity are not
independent premises. Validator error/fail/div branches remain in the original
consumer; the theorem concerns successful decoding/validation selection.

`publicAdmission` supplies the exact named law:

```
forall pub semantic,
  decodeSemantic installed pub = ok (some semantic) ->
  75 + pub.val.length <= SelectedTranscriptParams.L
```

The bound is 75+1880=1955 ≤131072, from the adopted full-forest public format,
not ASQ8 or payment216. `accepted_transport` applies the unchanged physical
byte-entry theorem with this concrete law. It adds no physical/logical input
gate and preserves arbitrary submitted public/stored bytes.

`S6CurrentByteSubstitutionV1.substitute` then applies the original complete
two-pass source-driver consumer, retaining its ordered-read/state equality and
same returned checkpoint. Before, that theorem took arbitrary adapter Ops and
`PublicAdmission adapter`. After, the adapter is the concrete current codec/
first installation and the admission premise is discharged. This is a proved
specialization, not a law for every arbitrary Ops record.

Exact retained premises: library `TrustedStd` (the existing two pure std laws),
all thirteen `BodyJoins source model`, source and model dictionaries, hash
interpretation, arbitrary byte submission and successful source byte entry.
No body join or identification of model with frozen2 is proved here. Actual
native SDK, source lowering and leaf/oracle interpretations remain outside
this port closure. No hypothetical native operation is replaced by an opaque
`.done` carrier or a convenient model dictionary.

Validation: two smallest changed targets compiled individually with the shared
atomic local lock, `lake env lean -j1 -M4400`, exit 0. Total wall 146.807028709
seconds, peak RSS 4,508,450,816 bytes, zero swap. Four public theorem axiom
reports contain only `propext`, `Classical.choice`, `Quot.sound`. Attempt v1 of
the admission file failed on namespace resolution and is excluded; final
admission v2 and substitution v1 are accepted. One harmless linter suggestion
was left in the accepted source rather than replaying for cosmetic cleanup.

Exact sources, commands, source revisions/hashes, tools, imports and metrics
are in `evidence/s126-current-caller-20261021/s6-current-public-admission-v2`
and `s6-current-byte-substitution-v1`. Associated `s6-current-public-admission-`
import/tool/reused pins identify the selected cached closure. The unchanged
Port1 Driver, ByteDriver, DriverSubstitution and CanonicalAudit source and
green receipts are retained under `s6-current-public-admission-reused`; their
hashes match current research. No unchanged full replay or binary distribution
was performed. Release authority/source pins remain those stated in
`S126-CURRENT-CALLER-INSTALLATION-20261024.md`; no adoption is inferred.

Audit: `python3 tools/s6-full-forest-roundtrip-20261023/check-public-admission.py`.
The next source obligations are the actual native operation interpretations
and the same-state/order model joins, including S1 prepare/op7, not another
public-size premise or an independent encoder-success assumption.
