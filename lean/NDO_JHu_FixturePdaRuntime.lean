import NDO_JHs_PDA
import NDO_JHj_RegistrySeeds
set_option autoImplicit false
namespace AspisR1.JHu_FixturePdaRuntime
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Exactly the seven reached fixture calls. -/
inductive Call : Slice (Slice U8) → solana_pubkey.Pubkey → Prop
  | master : Call JHj_Seeds.master JHb_Programs.pool
  | checkpoint : Call JHj_Seeds.checkpoint JHb_Programs.pool
  | lane : Call JHj_Seeds.lane JHb_Programs.pool
  | registry : Call JHj_RegistrySeeds.registry JHb_Programs.registry
  | registryProgramdata : Call JHj_RegistrySeeds.registryProgramdata JHj_RegistryValue.loader
  | entry : Call JHj_RegistrySeeds.entry JHb_Programs.registry
  | verifierProgramdata : Call JHj_RegistrySeeds.verifierProgramdata JHj_RegistryValue.loader

/-- For the seven explicitly enumerated JHs fixture PDA invocations, with the
pinned solana-pubkey 2.4.0 ABI, valid readable seed descriptors/bytes and
program-id bytes, valid disjoint writable output, and sufficient runtime
compute admission, sol_create_program_address agrees with the guarded
JHs_PDA.derive model: ordered seed concatenation, program-id bytes and ASCII
ProgramDerivedAddress are hashed using the existing runtime SHA semantics;
the exact digest is rejected iff the pinned curve25519-dalek 4.1.3 compressed
Edwards-Y decompressor succeeds. The model OnCurve square-root predicate
agrees with that decompressor, including its handling of noncanonical Y
encodings and the sign bit. A successful syscall writes exactly the digest
and returns zero; an on-curve digest returns InvalidSeeds (1). Seed-limit
failures are handled by the SDK wrapper before the syscall. Traps, invalid
memory, exhausted compute, unlisted calls and other runtime effects are
excluded. This row supplies no concrete digest equation, no off-curve fact,
no decoder result, no caller acceptance, and no artifact identity.

This is an explicit hypothesis, not an adopted trust row or an axiom.
The operation equality below is its value projection on the seven valid
fixture calls; runtime ABI/memory/compute admission are exactly the conditions
in the quoted statement, not independently proved by this module. -/
def FixturePdaRuntime (base : Ops) : Prop :=
  ∀ seeds program, Call seeds program → base.op38 seeds program=JHs_PDA.derive seeds program

end AspisR1.JHu_FixturePdaRuntime
