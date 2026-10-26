import R1Z.PV_L2_F5
import R1Z.PhaseWireLog2Bin

/-! Logical opening-address factoring on the actual deployed decoder.
Native sort/dedup, allocation and collection cost refinement is separate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F6Openings
open R0Z.FsStatement R0Z.JointView R1Z.GamesR1 R1Z.PhaseWireLog2Bin
  R1Z.PhaseSamplerParserBin R1Z.PhaseQueryScanBin
attribute [local instance] Classical.propDecidable
local notation "K" => PrivacyR1AcctBasis.K

/-- Neither field payloads nor other challenge coordinates influence the
logical reads; the whole ordered list, including cross-batch repeats, stays. -/
theorem opens_queries (ch ch' : Challenges K) (he : ch.queries = ch'.queries) :
    opens ch = opens ch' := by
  unfold opens reads batchFib batchQueries treeFib
  rw [he]

theorem parser_prefix_opens (s s' : Fin 27 → OracleAnswer)
    (o o' : Fin 4 → OracleAnswer) (q q' : Fin 8 → OracleAnswer)
    (rho rho' : OracleAnswer) (he : PrefixAgree q q' (stop done q)) :
    opens (decode s o q rho) = opens (decode s' o' q' rho') := by
  apply opens_queries
  exact (query_prefix q q' he).2

/-- The two batches' actual disclosure order and folded-tree addresses. -/
theorem parser_queries (s : Fin 27 → OracleAnswer) (o : Fin 4 → OracleAnswer)
    (q : Fin 8 → OracleAnswer) (rho : OracleAnswer) :
    (decode s o q rho).queries = querySet q := rfl

#print axioms opens_queries
#print axioms parser_prefix_opens
#print axioms parser_queries
end R1Z.PV_L2_F6Openings
