import NJE_WellSource

set_option autoImplicit false
noncomputable section
namespace NJE_WellPacket
open Aeneas Aeneas.Std Result

-- Exact returning value and ordered boundary count of NJE_well_entry_cut.
-- Native pointer/length assertions attach both replies to this SAME input.
def Cut (xs : List U32) (ordered domain out : Bool) (calls : Nat) : Prop :=
 out=(!xs.isEmpty && decide (xs.length≤16) && ordered && domain) ∧
 calls=(if xs.isEmpty || decide (xs.length>16) then 0 else if ordered then 2 else 1)

def ordered (xs : List U32) : Bool := (NJA_WellIteration.windows xs).all NJE_WellSource.order
def domain (xs : List U32) : Bool := xs.all NJE_WellSource.domain

theorem emitted_value (xs : List U32) :
    NJE_WellSource.emitted xs=
      ok (!xs.isEmpty && decide (xs.length≤16) && ordered xs && domain xs) := by
 unfold NJE_WellSource.emitted ordered domain
 rw [NJE_WellSource.all_result,NJE_WellSource.all_result]
 by_cases empty : xs.isEmpty=true
 · simp [empty]
 · by_cases small : xs.length≤16
   · by_cases o : (NJA_WellIteration.windows xs).all NJE_WellSource.order=true <;> simp [empty,small,o]
   · simp [empty,small]

theorem TX1_128 (xs : List U32) (out : Bool) (calls : Nat)
    (cut : Cut xs (ordered xs) (domain xs) out calls) :
    NJE_WellSource.emitted xs=ok out ∧
    out=decide (AspisR1.OraclePortFrozenOrder.wellFormed (xs.map (fun x : U32 => x.val))) := by
 have source := NJE_WellSource.source xs
 have reply : NJE_WellSource.emitted xs=ok out := by rw [emitted_value,cut.1]
 exact ⟨reply,(Result.ok.inj (reply.symm.trans source)).trans (NJA_WellFormed.source_eq _)⟩

theorem TX2_094 (xs : List U32) (out : Bool) (calls : Nat)
    (cut : Cut xs (ordered xs) (domain xs) out calls) :
    NJE_WellSource.emitted xs=ok out ∧
    out=decide (AspisR1.OraclePortFrozenOrder.wellFormed (xs.map (fun x : U32 => x.val))) := TX1_128 xs out calls cut

#print emitted_value
#print axioms emitted_value
#print TX1_128
#print axioms TX1_128
#print TX2_094
#print axioms TX2_094
end NJE_WellPacket
end
