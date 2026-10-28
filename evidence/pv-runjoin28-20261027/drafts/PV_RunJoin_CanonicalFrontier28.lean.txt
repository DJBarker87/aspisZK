import R1Z.PV_Src_CanonicalSnapshot
import R1Z.PV_RunJoin_FrontierHonesty28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalFrontier28
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open PV_Src_NativeInput

/-- Canonical encoding supplies the frontier fact before compilation. The
association must be proved for the actual preparation inputs; successful
compilation by itself cannot replace it. Only frontier equality is needed. -/
theorem frontier_of_encoding (i : Input) (pub : R0P.Public F)
    (bound : pub.nextPairIndex < 2^64)
    (pool domain : PV_Src_PublicRecords.Context)
    (encoded : i.snapshot.frontier = (PV_Src_CanonicalSnapshot.native pub bound pool domain).frontier)
    (l : Fin 20) : Canon8 i.snapshot.frontier.val[l.val]! := by
  rw [encoded]
  exact PV_Src_CanonicalSnapshot.frontier_canonical pub bound pool domain l
#print axioms frontier_of_encoding

theorem probe_excluded_by_encoding (pub : R0P.Public F)
    (bound : pub.nextPairIndex < 2^64) (pool domain : PV_Src_PublicRecords.Context) :
    PV_RunJoin_FrontierHonesty28.frontier ≠
      (PV_Src_CanonicalSnapshot.native pub bound pool domain).frontier := by
  intro same
  have hc := PV_Src_CanonicalSnapshot.frontier_canonical pub bound pool domain
    (⟨0,by decide⟩ : Fin 20) 0 (by decide)
  rw [← same] at hc
  change PV_RunJoin_FrontierHonesty28.frontier.val[0]!.val[0]!.val < 2147483647 at hc
  rw [PV_RunJoin_FrontierHonesty28.raw_word] at hc
  omega
#print axioms probe_excluded_by_encoding
end R1Z.PV_RunJoin_CanonicalFrontier28
