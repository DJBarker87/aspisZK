import S9ConstructorV3StatementProducerSemanticsV1
import S9ConstructorV3RetainedPointModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3OpeningPointsJoinV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3CarryBodySemanticsV1
open AspisR1S9ConstructorV3VectorMeaningV1
open AspisR1S9ConstructorV3DecodedInputV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ConstructorV3StatementProducerSemanticsV1
open AspisR1S9ConstructorV3RetainedPointModelV1

/-- Same successful source producer, interpreted in the existing retained
openingPoints definition, with the source MSB→model LSB reversal explicit.
The two read equations identify the actual returned word, not child arithmetic
or initial-state correctness assumptions. -/
theorem source_points_success_openingPoints
    (z : Vector) (points : StatementPoints) (hz : VectorCanonical z)
    (hsource : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points z = .ok points)
    (which : Fin 3) (coordinate : Fin 10) (rowIndex cellIndex : Usize)
    (hrowIndex : rowIndex.val=which.val) (hcellIndex : cellIndex.val=coordinate.val)
    (row : Vector) (q : Q)
    (hrow : Array.index_usize points rowIndex = .ok row)
    (hcell : Array.index_usize row cellIndex = .ok q) :
    decode q = R0P.SemSource.openingPoints
      (fun i : Fin 10 => decodedInput z i.val) which
      ⟨9-coordinate.val,by omega⟩ := by
  have hp := statement_points_success_exact z points hz hsource rowIndex row hrow cellIndex q hcell
  rw [hrowIndex,hcellIndex] at hp
  have hrevNat : 9-(9-coordinate.val)=coordinate.val := by omega
  have hrevFin : (⟨9-(9-coordinate.val),by omega⟩ : Fin 10)=coordinate := by
    apply Fin.ext
    exact hrevNat
  have hkbound := which.isLt
  have hkcases : which.val=0 ∨ which.val=1 ∨ which.val=2 := by omega
  rcases hkcases with hk0 | hk1 | hk2
  · have hk : which=0 := Fin.ext hk0
    subst which
    change decode q=decodedInput z coordinate.val at hp
    simpa only [R0P.SemSource.openingPoints,R0P.SemSource.toR0,hrevNat] using hp
  · have hk : which=1 := Fin.ext hk1
    subst which
    change decode q=successorPoint (decodedInput z) coordinate.val at hp
    rw [successorPoint_eq_retained (decodedInput z) coordinate] at hp
    simpa only [R0P.SemSource.openingPoints,R0P.SemSource.toR0,hrevFin] using hp
  · have hk : which=2 := Fin.ext hk2
    subst which
    change decode q=xor12Point (decodedInput z) coordinate.val at hp
    have hx : xor12Point (decodedInput z) coordinate.val = R0P.SemSource.xor12Point
        (fun i : Fin 10 => decodedInput z i.val) coordinate := rfl
    rw [hx] at hp
    simpa only [R0P.SemSource.openingPoints,R0P.SemSource.toR0,hrevFin] using hp

#print axioms source_points_success_openingPoints
end AspisR1S9ConstructorV3OpeningPointsJoinV1
