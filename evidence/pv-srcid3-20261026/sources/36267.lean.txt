import R1Z.PV_Src_CheckedCanonical
import R1Z.PV_Src_NativeIdentification

/-! Genuine omission of the words field for the canonical native encoding
under the explicit dynamic reference dictionary. No Checked premise appears
in the remainder: it is proved for every encoded input. Actual installed
input selection and unstubbed mapper association are not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_SelectedFour
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_NativeInput PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
variable [ExternalLinear]
local instance : Records := PV_Src_RecordDynamic.dictionary

structure Remainder {I : Type} (selected : I → PV_Src_CheckedCanonical.Data (K := K))
    (transport : Fin 1024 ≃ Fin 1024) : Prop where
  compile_call : ∀ i,
    run (PV_Src_CheckedCanonical.input (selected i)) = ok (.Ok (PV_Src_CheckedCanonical.input (selected i)).compiled)
  publicCorr : ∀ i records,
    newRecords (PV_Src_CheckedCanonical.input (selected i)) = ok records →
    PubCorr (wordPublic records.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (PV_Src_CheckedCanonical.input (selected i)))))
  admission : ∀ i records,
    newRecords (PV_Src_CheckedCanonical.input (selected i)) = ok records →
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (PV_Src_CheckedCanonical.input (selected i)))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

variable {I : Type} {selected : I → PV_Src_CheckedCanonical.Data (K := K)}

def complete {transport : Fin 1024 ≃ Fin 1024} (p : Remainder (K := K) selected transport) :
    PV_Src_NativeIdentification.PV_Src_Premises (K := K)
      (fun i => PV_Src_CheckedCanonical.input (selected i)) transport where
  compile_call := p.compile_call
  words := fun i => PV_Src_CheckedCanonical.words (selected i)
  publicCorr := p.publicCorr
  admission := p.admission
  row_call := p.row_call

def identification {transport : Fin 1024 ≃ Fin 1024} (p : Remainder (K := K) selected transport) :=
  PV_Src_NativeIdentification.identification (complete p)

#print Remainder
#print axioms complete
#print axioms identification
end R1Z.PV_Src_SelectedFour
