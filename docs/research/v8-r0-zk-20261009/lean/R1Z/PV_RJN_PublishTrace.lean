import R1Z.PV_RJN_Bytes
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RJN_PublishTrace
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]
abbrev V := alloc.vec.Vec U8
/-- Only the source calls and guards reached by a successful publication.
No model byte list or model assembly occurs in this trace. -/
def Trace (variant : transport.Variant) (p : prover.Publication) (proof : V) : Prop :=
  ∃ (size openings nodes : Usize) (magic : Array U8 8#usize) (tag : U8)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : V) (ib : Array U8 32#usize)
    (cc1 cc2 : host_commitment.Commitment)
    (semanticResult valuesResult : core.result.Result Unit compact.CodecError),
    compact.PROOF_BYTES=ok size ∧ compact.MAGIC=ok magic ∧ transport.Variant.tag variant=ok tag ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 size)
      magic.to_slice=ok h0 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 h0
      (Array.make 8#usize [tag,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]).to_slice=ok h1 ∧
    host_compact.compact_semantic (alloc.vec.Vec.deref p.semantic_bytes) h1=ok (semanticResult,h2) ∧
    host_compact.compact_values (alloc.vec.Vec.deref p.y1) h2=ok (valuesResult,h3) ∧
    aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive=ok ib ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 h3 ib.to_slice=ok h4 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 h4 (alloc.vec.Vec.deref p.c0bytes)=ok h5 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 h5 p.root.to_slice=ok h6 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 h6 (alloc.vec.Vec.deref p.c1bytes)=ok h7 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 h7 (alloc.vec.Vec.deref p.fbytes)=ok h8 ∧
    compact.OFF_OPENINGS=ok openings ∧ alloc.vec.Vec.len h8=openings ∧
    p.backend.c1=some cc1 ∧ p.backend.c2=some cc2 ∧
    prover.append_query_openings h8 cc1 cc2 p.queries (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok h9 ∧
    compact.OFF_NODES=ok nodes ∧ alloc.vec.Vec.len h9=nodes ∧
    prover.append_node_slots h9 cc1 cc2 p.tree p.queries=ok (.Ok proof) ∧ alloc.vec.Vec.len proof=size

theorem source (variant : transport.Variant) (p : prover.Publication) (proof : V)
    (h : prover.publish_compact variant p=ok (.Ok proof)) : Trace variant p proof := by
  unfold prover.publish_compact at h
  obtain ⟨size,hsize,h⟩ := bind_eq_ok h
  obtain ⟨magic,hmagic,h⟩ := bind_eq_ok h
  try simp only [lift,bind_tc_ok] at h
  obtain ⟨h0,hh0,h⟩ := bind_eq_ok h
  obtain ⟨tag,htag,h⟩ := bind_eq_ok h
  try simp only [lift,bind_tc_ok] at h
  obtain ⟨h1,hh1,h⟩ := bind_eq_ok h
  obtain ⟨pair,hsem,h⟩ := bind_eq_ok h
  rcases pair with ⟨semanticResult,h2⟩
  obtain ⟨r,hmapped,h⟩ := bind_eq_ok h
  cases r with
  | Err e => cases h
  | Ok u =>
    cases u
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨pair,hclaim,h⟩ := bind_eq_ok h
    rcases pair with ⟨valuesResult,h3⟩
    obtain ⟨r,hmapped2,h⟩ := bind_eq_ok h
    cases r with
    | Err e => cases h
    | Ok u =>
      cases u
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨ib,hib,h⟩ := bind_eq_ok h
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨h4,hh4,h⟩ := bind_eq_ok h
      obtain ⟨h5,hh5,h⟩ := bind_eq_ok h
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨h6,hh6,h⟩ := bind_eq_ok h
      obtain ⟨h7,hh7,h⟩ := bind_eq_ok h
      obtain ⟨h8,hh8,h⟩ := bind_eq_ok h
      obtain ⟨openings,hopen,h⟩ := bind_eq_ok h
      by_cases hopenlen : alloc.vec.Vec.len h8=openings
      · simp only [massert,hopenlen,if_true,bind_tc_ok] at h
        cases hc1 : p.backend.c1 with
        | none => simp only [hc1,core.option.Option.take,core.option.Option.unwrap,ofOption,bind_tc_fail] at h; cases h
        | some cc1 =>
          simp only [hc1,core.option.Option.take,core.option.Option.unwrap,ofOption,bind_tc_ok] at h
          cases hc2 : p.backend.c2 with
          | none => simp only [hc2,core.option.Option.take,core.option.Option.unwrap,ofOption,bind_tc_fail] at h; cases h
          | some cc2 =>
            simp only [hc2,core.option.Option.take,core.option.Option.unwrap,ofOption,bind_tc_ok] at h
            obtain ⟨h9,hh9,h⟩ := bind_eq_ok h
            obtain ⟨nodes,hnodes,h⟩ := bind_eq_ok h
            by_cases hnodelen : alloc.vec.Vec.len h9=nodes
            · simp only [massert,hnodelen,if_true,bind_tc_ok] at h
              obtain ⟨r,hn,h⟩ := bind_eq_ok h
              cases r with
              | Err e => cases h
              | Ok val =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                by_cases hlen : alloc.vec.Vec.len val=size
                · simp only [massert,hlen,if_true,bind_tc_ok] at h
                  cases h
                  exact ⟨size,openings,nodes,magic,tag,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,ib,cc1,cc2,semanticResult,valuesResult,
                    hsize,hmagic,htag,hh0,hh1,hsem,hclaim,hib,hh4,hh5,hh6,hh7,hh8,hopen,hopenlen,
                    hc1,hc2,hh9,hnodes,hnodelen,hn,hlen⟩
                · simp only [massert,hlen,if_false] at h; cases h
            · simp only [massert,hnodelen,if_false] at h; cases h
      · simp only [massert,hopenlen,if_false] at h; cases h
#print axioms source
end R1Z.PV_RJN_PublishTrace
