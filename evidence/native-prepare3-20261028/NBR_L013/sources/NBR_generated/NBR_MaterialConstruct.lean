import NBR_BlockConstruct
import NBL_MaterialTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBR_MaterialConstruct
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_BlockTrace NBL_MaterialTrace

theorem pair {H : Type} (D : aspis_core.Digest32 H) (total : NBR_BlockConstruct.Total D)
    (hash : H) (before : Bytes32) : Nonempty (Pair D hash before) := by
  obtain ⟨block,readCall⟩ := total hash (NBA_Transcript.readParts before 1#u8)
  obtain ⟨advance,advanceCall⟩ := total hash (NBA_Transcript.readParts before 2#u8)
  exact ⟨⟨block,advance,readCall,advanceCall⟩⟩

/-- All eight eager pairs are constructed in order on ONE state carrier.
No eight-block materialization or decoder Result is a hypothesis. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (total : NBR_BlockConstruct.Total D)
    (hash : H) (before : Bytes32) : Nonempty (Trace D hash before) := by
  obtain ⟨p0⟩ := pair D total hash before
  obtain ⟨p1⟩ := pair D total hash p0.advance
  obtain ⟨p2⟩ := pair D total hash p1.advance
  obtain ⟨p3⟩ := pair D total hash p2.advance
  obtain ⟨p4⟩ := pair D total hash p3.advance
  obtain ⟨p5⟩ := pair D total hash p4.advance
  obtain ⟨p6⟩ := pair D total hash p5.advance
  obtain ⟨p7⟩ := pair D total hash p6.advance
  exact ⟨⟨p0,p1,p2,p3,p4,p5,p6,p7⟩⟩

#print axioms pair
#print axioms source
end AspisR1.NBR_MaterialConstruct
end
