# NDZ identity gate: PASS

Frozen verifier source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Inspection worktree HEAD: dfa35acd8390aea176c13710d320d041332b320a.
The inspected production files have no diff against the frozen revision.

`programs/r1-cost-probe/src/lib.rs:56–64` forwards the invocation's program ID
into the adapter. There is no declare_id/check_id or fixed verifier ID in the
production route. Adapter `:212–218` checks checkpoint ownership against that
runtime ID; `:523–625` authenticates the selected verifier against registry
entry data and derives its loader ProgramData from the runtime ID. The only
compiled deployment addresses are Pool and registry (`:79–96`), which remain
unchanged. No self-ID constant is used for PDA derivation.

NDZ_ELF_SCAN.json records a fresh SHA256/size of the supplied release ELF:
1,563,728 bytes, 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299.
Its Pool/registry byte slots occur at offsets 1526640/1526672. Neither the
historical verifier ID, legacy verifier ID, nor the build-generated public key
occurs as raw 32 bytes or ASCII in it. The build key public identity was obtained
using solana-keygen pubkey on the host; no secret bytes were inspected or copied.
A byte scan alone is not a proof of absence of constructed constants; it
corroborates the source inspection and reused NCY source-to-ELF reproduction.

Read-only `solana program dump` fetched the deployed Pool, registry and carrier
ELFs. Their hashes match the repository pins (NDZ_ELF_SCAN.json); Pool and
registry contain none of the three verifier identities above. Pool
`pair_forest_dispatch.rs:194–215` selects/authenticates the supplied verifier
through entry data; registry `processor.rs:989–1030` accepts the verifier ID as
instruction data and authenticates its immutable loader deployment. Neither
requires a particular verifier address. An unchanged release ELF can therefore
be deployed at a fresh address without a self-ID rebuild.

Fresh-state route is supported by existing code: Pool
`pair_forest.rs:1994–2078` derives a new master from the supplied mint, prepares
fresh master/lanes/vault, and creates their PDAs. Registry
`processor.rs:910–982` accepts a supplied Pool address, derives a fresh V2
registry for it and stores its policy/authority. Schedule/activate/freeze are
`:983`, `:1072`, `:1189`; no old Pool state is referenced. Pool policy's fresh
registry must be immutable before spending. The spend driver initializes Pool
before the registry; this is valid because initialization stores policy and
does not authenticate an existing registry. No migration or old-state rewiring
is claimed.

No public writes, public transaction simulations/signatures, key generation,
build, or local transactions were needed for this gate. Read-only payer check:
CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t, mode 0600, 18.35320408 SOL.
