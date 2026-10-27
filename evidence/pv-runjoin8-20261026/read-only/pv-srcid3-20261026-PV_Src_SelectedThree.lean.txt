import R1Z.PV_Src_FrozenPublic
import R1Z.PV_Src_NativeIdentification

/-! words and publicCorr are omitted, proved from canonical encoding and the
existing compile_call. This explicit P6-candidate uses the fixed-root owned
record reference and extracted external callback. Actual installation is not
asserted. RspendPlus and installed transport remain unchanged obligations. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_SelectedThree
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
local instance : Records := PV_Src_FrozenInput.records
local instance : ExternalLinear := PV_Src_FrozenInput.external

structure Remainder {I : Type} (selected : I → PV_Src_FrozenInput.Data (K := K))
    (transport : Fin 1024 ≃ Fin 1024) : Prop where
  compile_call : ∀ i, run (PV_Src_FrozenInput.input (selected i)) =
    ok (.Ok (PV_Src_FrozenInput.input (selected i)).compiled)
  admission : ∀ i records, newRecords (PV_Src_FrozenInput.input (selected i)) = ok records →
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (PV_Src_FrozenInput.input (selected i)))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

variable {I : Type} {selected : I → PV_Src_FrozenInput.Data (K := K)}

def complete {transport : Fin 1024 ≃ Fin 1024} (p : Remainder (K := K) selected transport) :
    PV_Src_NativeIdentification.PV_Src_Premises (K := K)
      (fun i => PV_Src_FrozenInput.input (selected i)) transport where
  compile_call := p.compile_call
  words := fun i => PV_Src_FrozenInput.words (selected i)
  publicCorr := fun i => PV_Src_FrozenPublic.correspondence (selected i) (p.compile_call i)
  admission := p.admission
  row_call := p.row_call

def identification {transport : Fin 1024 ≃ Fin 1024} (p : Remainder (K := K) selected transport) :=
  PV_Src_NativeIdentification.identification (complete p)

#print Remainder
#print axioms complete
#print axioms identification
end R1Z.PV_Src_SelectedThree
