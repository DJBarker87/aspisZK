# Compiler success alone does not ensure the HonestInput frontier condition

Checked native source-success instance: `pv28-frontier-01/receipt.json`, exit0,
optimized release build; canonical control succeeds. Checked Lean exclusion:
`FrontierHonesty28.every_payload_not_honest`, attempt38158, standard axioms.

The actual frozen withdrawal wrapper succeeds with input1000, amount250,
change750, the original canonical note/membership/super-root fixture, matching
public/context bindings, and a snapshot at sequence/index1 whose active
frontier[0] is eight raw M31 words equal toP=2147483647. The snapshot root is
freshly reconstructed from exactly this frontier and the frozen empty roots.
Tree validation succeeds. The returned compilation is fresh and preserves
this snapshot; no cached payload is changed. The separate snapshot encoder
rejects the same snapshot with NonCanonicalDigest.

`FrontierHonesty28.noncanonical_excludes` proves for every Input and payload
that a frontier[0][0] word equal toP violates HonestInput's Canon8 clause.
`every_payload_not_honest` specializes it to the native probe's argument
shape, quantifying over every root and returned compilation. Thus there is
no need to invent a replacement cached compilation or prove a large concrete
Lean run just to establish the representation obstruction.

This refutes the unrestricted implication from SUCCESS OF THESE RAW WRAPPERS
to HonestInput. It does not refute a preparation pipeline that first uses a
canonical encoder/decoder, nor the accepted V152–V154 theorem on HonestInput.
The existing canonical encoder's frontier theorem explicitly excludes this
probe. An actual caller-to-encoder/decoder association is therefore material;
it cannot be replaced by compiler success. No such association is assumed.
This is not a privacy distinguisher and removes no endpoint premise. It does
not show that an account decoder or the intended canonical encoder produces
these raw arguments.

The source mechanism is precise: late_append's tree validation checks that
inactive frontier slots equal empty roots and reconstructs the root from
active slots. It does not enforce canonical limbs in active slots. The
snapshot codec has that additional check; the compiler wrapper does not call
it. The checked native instance exercises a changed active word, with a
matching freshly recomputed root, rather than merely corrupting a valid root.

The full-withdrawal owner packet remains untouched: neither choice of honest
user domain nor a frozen compiler change is assumed. This finding concerns
a separate representation/provenance prerequisite. To prove the requested
successful-output theorem on the intended canonical route, identify and prove
that route's actual snapshot canonicality before composition. The raw wrapper
implication cannot serve as that theorem.
