import CurrentPreparedQueryLegality
import AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation
local notation "PrepWide" => aspis_core.field.WideExact
local notation "IndexedWide" => AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact

def prepToIndexedWide (x : PrepWide) : IndexedWide :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

def toBytesSource (x : PrepWide) : Result (Array U8 32#usize) :=
  AspisR1WideToBytesIndexedCandidate.field.wide_exact.WideExact.to_le_bytes (prepToIndexedWide x)

def toBytesExpected (x : PrepWide) : Array U8 32#usize :=
  AspisR1WideToBytesIndexedCandidate.expectedBytes (prepToIndexedWide x)

theorem toBytesSource_success (x : PrepWide) : toBytesSource x=ok (toBytesExpected x) :=
  AspisR1WideToBytesIndexedCandidate.indexed_candidate_to_le_bytes (prepToIndexedWide x)

def withIndexedToBytes (sampling : PreparedModel.Boundaries) : PreparedModel.Boundaries :=
  {sampling with toBytes:=toBytesSource}

theorem installed_indexed_toBytes (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result PrepWide) (x : PrepWide) :
    (installedBoundaries (withIndexedToBytes sampling) embed).toBytes x=ok (toBytesExpected x) :=
  toBytesSource_success x

#print axioms toBytesSource_success
#print axioms installed_indexed_toBytes
end AspisR1ClaimPreparedBridge.InstalledMeaning
