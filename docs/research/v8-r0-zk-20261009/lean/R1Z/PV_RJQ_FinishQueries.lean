import R1Z.PV_RJQ_TranscriptRange
import R1Z.PV_RunJoin_FinishContext47
set_option autoImplicit false
namespace R1Z.PV_RJQ_FinishQueries
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost PV_RJQ_QueryInvariant
variable [ExternalTypes] [ExternalFuns]
theorem run (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts)
    (round : Result (Array aspis_core.field.wide_exact.WideExact 7#usize))
    (fold : aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
    (p : prover.Publication)
    (h : PV_RunJoin_FinishContext47.run variant hash prepared salts round fold=ok (.Ok p)) :
    Bounded p.queries := by
  unfold PV_RunJoin_FinishContext47.run at h
  obtain ⟨leaves,hleaves,h⟩ := bind_eq_ok h
  obtain ⟨o,htree,h⟩ := bind_eq_ok h
  obtain ⟨r,hr,h⟩ := bind_eq_ok h
  cases r with
  | Err e => cases h
  | Ok tree =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨root,hroot,h⟩ := bind_eq_ok h
    obtain ⟨second,hsecond,h⟩ := bind_eq_ok h
    simp only [lift,bind_tc_ok] at h
    obtain ⟨cbytes,hcbytes,h⟩ := bind_eq_ok h
    obtain ⟨payload,hpayload,h⟩ := bind_eq_ok h
    obtain ⟨payload1,hpayload1,h⟩ := bind_eq_ok h
    obtain ⟨pair,halpha,h⟩ := bind_eq_ok h
    rcases pair with ⟨alpha,transcript⟩
    obtain ⟨final,hfinal,h⟩ := bind_eq_ok h
    obtain ⟨fbytes,hfbytes,h⟩ := bind_eq_ok h
    obtain ⟨pair,hqueries,h⟩ := bind_eq_ok h
    rcases pair with ⟨r,next⟩
    simp only [Aeneas.Std.uncurry_apply_pair] at h
    cases r with
    | Err e => cases h
    | Ok queries =>
      have bounded := PV_RJQ_TranscriptRange.source
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 transcript 31#u8
        (alloc.vec.Vec.deref fbytes) queries next hqueries
      try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift] at h
      obtain ⟨tag32,htag32,h⟩ := bind_eq_ok h
      obtain ⟨z0,hz0,h⟩ := bind_eq_ok h
      obtain ⟨z1,hz1,h⟩ := bind_eq_ok h
      obtain ⟨v,hv,h⟩ := bind_eq_ok h
      obtain ⟨root0,hroot0,h⟩ := bind_eq_ok h
      obtain ⟨checked,hchecked,h⟩ := bind_eq_ok h
      cases checked with
      | Err e => cases h
      | Ok unit =>
        try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
        exact bounded

#print axioms run
end R1Z.PV_RJQ_FinishQueries
