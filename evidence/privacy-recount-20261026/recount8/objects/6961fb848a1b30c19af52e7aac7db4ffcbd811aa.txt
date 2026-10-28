import R1Z.PV_RunJoin_RuntimeMemory38
import R1Z.PV_RunJoin_RuntimeHash38
import R1Z.PV_RunJoin_RuntimeInit35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeBody38
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes]

structure Inputs where
  publicInput : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  hash : Slice (Slice U8) → Result (Array U8 32#usize)
  store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore

abbrev Secret := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Output :=
  (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore

def program (input : Inputs) (secret : Secret) :=
  PV_W_R_Entry.program input.publicInput input.compiled .S2
    (PV_RunJoin_RuntimeHash38.reify input.hash) secret input.store

variable {W S F D DF ZF C : Type}
def run (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (input : Inputs) (secret : Secret) : M W (Option C) Aeneas.Std.Error Output :=
  PV_W_Syntax.eval (PV_W_ReachedThreading.interpret (PV_RunJoin_RuntimeMemory38.algebra base memory))
    (program input secret)

/-- The exact complete actual source Result, with the original hash callback,
compiled payload, S2 variant, attempt secrets and returned store. Runtime
helper/OS/native adequacy is not inferred from this syntax-erasure theorem. -/
theorem source (ops : ExternalFuns) (input : Inputs) (secret : Secret) :
    PV_W_ReachedEffects.erase ops (program input secret) =
      @prover.prove_masked_attempt _ ops input.publicInput input.compiled .S2
        input.hash secret input.store := by
  rw [program,PV_W_R_Entry.erase_program,PV_RunJoin_RuntimeHash38.source]

variable {Coins E N L File Reply Time Worker Fs Allocator Extra : Type}
def initialized
    (data : PV_RunJoin_RuntimeInit35.Input Coins E N L File Reply Time Worker Fs Allocator Extra)
    (base : PV_W_TypedEffects.Algebra (PV_W_OsFile.Full E File Reply Time Worker Fs Allocator Extra)
      (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory (PV_W_OsFile.Full E File Reply Time Worker Fs Allocator Extra)
      S F D DF ZF) (input : Inputs) (secret : Secret) (c : Coins) :=
  run base memory input secret (PV_RunJoin_RuntimeInit35.world data c)

/-- This executes the recursively spliced actual body on the full initialized
world. Failure and divergence keep the same post-world and call prefix as
success. No Result-only decoder or native purity assumption is installed. -/
theorem initialized_executes
    (data : PV_RunJoin_RuntimeInit35.Input Coins E N L File Reply Time Worker Fs Allocator Extra)
    (base : PV_W_TypedEffects.Algebra (PV_W_OsFile.Full E File Reply Time Worker Fs Allocator Extra)
      (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory (PV_W_OsFile.Full E File Reply Time Worker Fs Allocator Extra)
      S F D DF ZF) (input : Inputs) (secret : Secret) (c : Coins) :
    PV_W_Syntax.Executes
      (PV_W_ReachedThreading.interpret (PV_RunJoin_RuntimeMemory38.algebra base memory))
      (program input secret) (PV_RunJoin_RuntimeInit35.world data c)
      (initialized data base memory input secret c) :=
  PV_W_Syntax.execution_complete _ _ _

#print axioms source
#print axioms initialized_executes
end R1Z.PV_RunJoin_RuntimeBody38
