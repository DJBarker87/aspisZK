import S1OwnedQueryPairsSourceV1
import S1ClosedPreparationHashCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisS1OwnedQueryDecoderInstallation
open Aeneas Aeneas.Std Result
open AspisS1OwnedQueryPairs AspisS1OwnedQueryPairs.Model
open AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared

def ownedDecode (blocks advances : Blocks) :=
  Query31ConcreteMaterializedSchedule.adaptScanResult (adapt (pairs_reference blocks advances))

/-- The actual decoder field used by the enclosing preparation model is the
concrete extracted owned driver. Equality is of the full Result, including
native error fields/fail/div, not just accepted query lists. -/
theorem closed_decoder_eq_owned : closedHashQueries.decode=ownedDecode := by
  funext blocks advances
  change Query31ConcreteMaterializedSchedule.actualConcreteDecode
    Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances=ownedDecode blocks advances
  unfold Query31ConcreteMaterializedSchedule.actualConcreteDecode ownedDecode
  have initial_eq : Query31ConcreteDriverTraceFacts.sourceDefaultState=project initial := rfl
  rw [initial_eq,reference_eq_source]

/-- Concrete replacement of one function field, with its exact equality proved
rather than an assumed dictionary contract. The embed operation is retained. -/
def ownedQueries : QueriesModel.Boundaries :=
  {closedHashQueries with decode:=ownedDecode}

theorem ownedQueries_eq : ownedQueries=closedHashQueries := by
  unfold ownedQueries
  rw [← closed_decoder_eq_owned]

/-- The complete enclosing preparation code keeps its result, scratch effects,
errors and digest nodes under the concrete owned query decoder installation.
No child success or query-model equivalence hypothesis is supplied. -/
theorem preparation_code_owned_eq {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    PreparedSourceEffects.prepare
      (PreparedHashCode.preparationEffects closedHashBoundaries ownedQueries) D sem view hash scratch=
    PreparedSourceEffects.prepare
      (PreparedHashCode.preparationEffects closedHashBoundaries closedHashQueries) D sem view hash scratch := by
  rw [ownedQueries_eq]

#print axioms closed_decoder_eq_owned
#print axioms ownedQueries_eq
#print axioms preparation_code_owned_eq
end AspisS1OwnedQueryDecoderInstallation
