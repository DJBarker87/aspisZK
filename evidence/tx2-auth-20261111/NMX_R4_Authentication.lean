import NMX_R4_BoxBinding
import NMX_R4_SourceFold
import NMX_R4_AllArgs
set_option autoImplicit false
noncomputable section
namespace NMX_R4_Authentication
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel

/-- Private allocation labels are pairwise distinct. They retain all four
owned payloads and do not assert that a label is a physical pointer. -/
def owners : Owners := ⟨0,1,2,3⟩

structure Choices where
 sites : RSL.TX2_233.Args → RSL.Env → NMX_R2_NativeExecution.Allocations
 lane : RSL.Bytes → RSL.Env → Bool
 registry : RSL.TX2_234.Args → RSL.Env → Nat → Bool

def context (choices : Choices) (a : RSL.TX2_233.Args) (env : RSL.Env) : NMX_R4_CallRun.Context :=
 ⟨owners,choices.sites a env,.panic,
  NMX_R3_LaneInstance.native owners.lane choices.lane,
  NMX_R2_CanonicalChildren.registry (NMX_R3_RegistryRoot.authenticate choices.registry),env⟩

/-- The actual emitted call script with its named std/SDK and CLOSED child
interpretations installed. No Ops, PoolLib, DeployedIds, child RowSpec or
representation hypothesis is retained by this implementation. -/
def authenticate (choices : Choices) (a : RSL.TX2_233.Args) (env : RSL.Env) :
 RSL.Obs (Except RSL.ProgramError RSL.Authenticated) :=
 if count : a.accounts.length = 7 then
   let native := NMX_R2_ArgsReify.reify (NMX_R4_ProjectionRef.args a) (NMX_R4_ArgsPort.bounds a count)
   let c := context choices a env
   NMX_R4_CallRun.observe c
    (NMX_R4_CallRoot.auth c.owners (NMX_R4_CallContext.ops c)
      native.program native.accounts native.pool native.lane native.slot)
 else ⟨.ret (.error (if a.accounts.length < 7 then .notEnoughAccountKeys else .invalidArgument)),[]⟩

/-- Full ordered-observation equality, before applying the canonical row law.
Only mathematically oversized data is projected; ProjectionRef proves equality
of the entire reference relation, including errors and stopped prefixes. -/
theorem observed (choices : Choices) (a : RSL.TX2_233.Args) (env : RSL.Env) :
 authenticate choices a env =
 NMX_R4_AllArgs.execution owners (choices.sites a env) .panic choices.lane choices.registry a env := by
 unfold authenticate NMX_R4_AllArgs.execution
 split
 · exact NMX_R4_SourceFold.source (context choices a env) _ _ _ _ _
 · rfl

/-- Canonical rev3 RowSpec with Domain=True and all allocation decisions.
The source association is observed, not inferred from value erasure. -/
theorem root (choices : Choices) :
 RSL.TX2_233.RowSpec_233 LIBB_PoolLib.library LIBB_PoolLib.deployed (authenticate choices) := by
 intro a env domain
 rw [observed]
 exact NMX_R4_AllArgs.operational owners (choices.sites a env) .panic choices.lane choices.registry a env domain

#print axioms observed
#print axioms root
end NMX_R4_Authentication
end
