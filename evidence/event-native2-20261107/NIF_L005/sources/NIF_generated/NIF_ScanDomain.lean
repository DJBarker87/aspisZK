import NIF_ScanEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_ScanDomain
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_Tx1Stages
open OraclePortCompactDraft MultiproofConeCanonical
/-- The scan's folded-field region, on the SAME proof and SAME query index. -/
theorem opening_fields (proof : Slice U8) (i : Nat) (inside : i<22)
 (scan : OraclePortCompactDraft.scan (bytesOf proof.val)) :
 canonical (slice (slice (bytesOf proof.val) (10055+i*832) 832) 672 128) := by
 exact (scan.2.2.2 i (List.mem_range.mpr inside)).2
/-- Reaching the query cut through the concrete scan installation establishes
canonical folded fields before any field decoder is invoked. -/
theorem reached_fields (base : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H) (c : Context)
 (length : proof.val.length=57607)
 (run : beforeQuery (Op4P_Install.install base) prepareCall D pub public_bytes proof k hash none=ok (.Ok c))
 (i : Nat) (inside : i<22) :
 canonical (slice (slice (bytesOf proof.val) (10055+i*832) 832) 672 128) := by
 have passed := NIF_ScanEntry.reached_scan (Op4P_Install.install base) prepareCall D pub public_bytes proof k hash c run
 have scan := Op4P_Install.scan_of_success proof length passed
 exact opening_fields proof i inside scan
#print axioms opening_fields
#print axioms reached_fields
end AspisR1.NIF_ScanDomain
