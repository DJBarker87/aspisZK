import R1Z.PV_Src_PackedSelection
import R1Z.PV_RunJoin_JoinedInstallation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PackedPublic
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Full source projection ignores recipient witness differences, but retains
all compiled public transition fields. No compiler execution is asserted. -/
theorem canonical_public (a b : PV_Src_CheckedCanonical.Data (K := K))
    (hp : a.canonical.val.1 = b.canonical.val.1)
    (pool : a.pool = b.pool) (domain : a.domain = b.domain)
    (destination : a.destination = b.destination)
    (transition : a.compiled.public_statement = b.compiled.public_statement) :
    PV_Src_NativeInput.publicInput (PV_Src_CheckedCanonical.input a) =
      PV_Src_NativeInput.publicInput (PV_Src_CheckedCanonical.input b) := by
  unfold PV_Src_CheckedCanonical.input PV_Src_CheckedEncoding.input
    PV_Src_NativeInput.publicInput PV_Src_CanonicalRequest.request
  rw [hp, pool, domain, destination, transition]
  cases b.canonical.val.1.variant <;> rfl

/-- Packed path selection preserves the full source public projection,
including the same supplied compiler payload. -/
theorem packed_public (i : PV_Src_CheckedCanonical.Data (K := K)) :
    PV_Src_NativeInput.publicInput (PV_Src_CheckedCanonical.input (PV_Src_PackedSelection.select i)) =
      PV_Src_NativeInput.publicInput (PV_Src_CheckedCanonical.input i) :=
  canonical_public _ _ (PV_Src_PackedSelection.public_preserved i) rfl rfl rfl rfl

#print axioms canonical_public
#print axioms packed_public
end R1Z.PV_RunJoin_PackedPublic
