# NBE replacements and domains

No kani::stub or stub_verified replacement is installed. No field arithmetic,
field multiplication or SHA computation is proved by NBE Kani gates.

| Backend | Meaning | Validation / domain |
|---|---|---|
| NBE_multiproof::Hash | Instantiated Digest32 observer, not a function stub; arbitrary32-byte answer; one selected byte of each32-byte parent input and call count | K010, occupied index<15 and sibling index<15; K013 extends sibling to index15. A byte coordinate is arbitrary<32; header and all part lengths are checked. |
| NBE_keys::Hash | Instantiated Digest32 observer with arbitrary32-byte reply | K002; actual batch_leaf, every tree<3, every address coordinate<480, same actual832-byte opening; all tags/part lengths and selected value/salt byte checked. |
| NBE_multiproof::NoHash | Actual Digest32 implementation that asserts if called | K005: native verify_in_place n=0 or n>16, no digest, selected arbitrary scratch coordinates unchanged. No success-path substitution. |
| NBE_multiproof::Counter | Instantiated Digest32 observer with arbitrary32-byte reply, no address assertion | K012 timed out and is EXCLUDED. K015 paired projection passed; K016 supplied-sibling projection timed out and is EXCLUDED; K017 short-sibling projection passed. Callback-address association is a SEPARATE obligation; passing state checks cannot close NodeGate or the whole verifier. |

Every observer returns its answer directly and is inlined by Kani. SHA is never
unwound. One row has at most one digest; replies are never reused to claim
multicall equality. The independent arbitrary coordinate and inherited
MultiproofConeNodeAdoption.array_ext support extensional conclusions only
within the checked domain. No passing instance establishes all slots or all
ordered multicall traces automatically.

There is no new multiplication-stub pairing for LPh_STUBS.md. The inherited
field tables are unmodified; no NBE result consumes an unpaired field stub.
