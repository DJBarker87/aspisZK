import R22TotalCheckedComposition
import PreparedFromQmSourceBridge
import AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11

/-! Exact indexed serializer and the literal carrier adapter used by
CurrentPreparedIndexedBytes. The function bodies are repeated in a distinct
namespace to avoid compiling or changing Session A's boundary-installation
module. Candidate adoption/current frozen caller identity is still external. -/
set_option autoImplicit false
namespace AspisR1.R22TotalIndexedByteCone
open Aeneas Aeneas.Std Result R22TotalCheckedComposition
abbrev PrepWide := AspisR1PublicPreparation.aspis_core.field.WideExact
abbrev IndexedWide := AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact

def prepToIndexedWide (x : PrepWide) : IndexedWide :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

def toBytesSource (x : PrepWide) : Result (Array U8 32#usize) :=
  AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes (prepToIndexedWide x)

def toBytesExpected (x : PrepWide) : Array U8 32#usize :=
  AspisR1WideToBytesIndexedCandidate.expectedBytes (prepToIndexedWide x)

theorem source_total (x : PrepWide) : toBytesSource x = ok (toBytesExpected x) :=
  AspisR1WideToBytesIndexedCandidate.indexed_candidate_to_le_bytes (prepToIndexedWide x)

theorem indexed_bytes_R22 (t : Translation toBytesSource) :
    ∀ x, NoOverflow (t.code x) ∧ wrapping (t.code x) = ok (toBytesExpected x) := by
  apply total_refinement_R22 t.code toBytesExpected
  intro x
  exact (t.source x).trans (source_total x)

#print axioms source_total
#print axioms indexed_bytes_R22
end AspisR1.R22TotalIndexedByteCone
