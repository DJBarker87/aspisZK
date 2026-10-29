import R1Z.PV_RJQ_QueryScan
import R1Z.ProverRwQueryCallerSplit
set_option autoImplicit false
namespace R1Z.PV_RJQ_TranscriptRange
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost PV_RJQ_QueryInvariant
variable [ExternalTypes] [ExternalFuns]
theorem source {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    (q : ProverRwQueryScan.Queries) (next : host_transcript.Transcript H)
    (h : host_transcript.Transcript.queries hash self row payload=ok (.Ok q,next)) :
    Bounded q := by
  rw [ProverRwQueryCallerSplit.queries_factor] at h
  obtain ⟨p,hp,h⟩ := bind_eq_ok h
  obtain ⟨r,hr,h⟩ := bind_eq_ok h
  cases r with
  | Err e => cases h
  | Ok value =>
    rcases value with ⟨queries,state⟩
    unfold ProverRwQueryPublish.publish at h
    obtain ⟨unit,ht,h⟩ := bind_eq_ok h
    cases h
    exact PV_RJQ_QueryScan.pairs p.2.1 p.2.2 _ _ hr
#print axioms source
end R1Z.PV_RJQ_TranscriptRange
