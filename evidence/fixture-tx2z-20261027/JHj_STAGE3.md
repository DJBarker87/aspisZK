# Corrected registry reads and explicit rejection semantics

JHj_RegistryReads/RegistryReadonly compute BOTH registry/entry physical reads and readonly metadata checks on JHg_World, retaining the actual 256/320-byte buffers despite the snapshots' historical 128/192 declared geometry. No callback changes are involved. JHj_RegistryReadStep/EntryReadStep join those reads to the supplied actual op33/op34 return; native decoder associations remain explicit. JHj_RegistryPolicyStep computes the immutable-deployment branch after precisely policy-validation and loader-ID observations.

The nine Master/Checkpoint/LanePda Error/Failure/Divergence roots preserve each factored PDA continuation's actual mapped InvalidAccountData, fail, and div outcomes. They are generic symbolic rejection checks, not claims that faithful native PDAs reject these bytes.

JHj_RegistryValue records expected fields and their retained-byte bindings; JHj_RegistryFields/EntryFields compute caller field comparisons on those records. These are NEVER installed as successful decoders. JHj_GuardNonVacuity.source joins six unconditional local comparison/mask facts, without any accepted/native result in the conjunction. Full authentication, joint accepted pair and headline non-vacuity are still open.

OBSTRUCTION70 is recorded. The remaining proof budget is reserved for grouped root/type/axiom audits, inherited JHi_ canonical roots and the separately pinned adopted headline, plus the small final registry-prefix composition. No broad package replay, shipped-source change, ELF rebuild, Kani or key operation occurred.
