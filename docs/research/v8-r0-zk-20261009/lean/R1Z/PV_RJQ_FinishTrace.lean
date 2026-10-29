import R1Z.PV_RunJoin_FinishContext47
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RJQ_FinishTrace
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
/-- Reachability facts only: no model Data/Plan or serializer conclusion. -/
def Trace (hash : Hash) (prepared : prover.PreparedOpening)
    (salts : host_commitment.PrivateSalts)
    (round : Result (Array W 7#usize))
    (fold : W → Result (alloc.vec.Vec W)) (p : prover.Publication) : Prop :=
  ∃ (leaves : alloc.vec.Vec (Array U8 32#usize)) (o : Option host_tree.BinaryTree) (tree : host_tree.BinaryTree)
    (root : Array U8 32#usize) (second : Array W 7#usize)
    (cbytes payload0 payload : alloc.vec.Vec U8) (alpha : W)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (final : alloc.vec.Vec W) (fbytes : alloc.vec.Vec U8)
    (queries : Array U32 22#usize)
    (next : host_transcript.Transcript aspis_core.digest.LegacyHashFn),
    prover.folded_leaves hash (alloc.vec.Vec.deref prepared.folded_word) salts=ok leaves ∧
    host_tree.BinaryTree.new aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash leaves=ok o ∧
    core.option.Option.ok_or o verifier.Error.Allocation=ok (.Ok tree) ∧
    host_tree.BinaryTree.root tree=ok root ∧ round=ok second ∧
    prover.encoded_slice second.to_slice=ok cbytes ∧
    alloc.slice.Slice.to_vec core.clone.CloneU8 root.to_slice=ok payload0 ∧
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 payload0 (alloc.vec.Vec.deref cbytes)=ok payload ∧
    host_transcript.Transcript.scalar aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      prepared.transcript 30#u8 (alloc.vec.Vec.deref payload) false=ok (alpha,transcript) ∧
    fold alpha=ok final ∧ prover.encoded_slice (alloc.vec.Vec.deref final)=ok fbytes ∧
    host_transcript.Transcript.queries aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
      transcript 31#u8 (alloc.vec.Vec.deref fbytes)=ok (.Ok queries,next) ∧
    p=⟨prepared.backend,prepared.sem.bytes,prepared.y1,prepared.inactive,
       prepared.c0bytes,root,cbytes,fbytes,queries,prepared.folded_word,salts,tree⟩

theorem run (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts)
    (round : Result (Array aspis_core.field.wide_exact.WideExact 7#usize))
    (fold : aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact))
    (p : prover.Publication)
    (h : PV_RunJoin_FinishContext47.run variant hash prepared salts round fold=ok (.Ok p)) :
    Trace hash prepared salts round fold p := by
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
        exact ⟨leaves,o,tree,root,second,cbytes,payload,payload1,alpha,transcript,
          final,fbytes,queries,next,hleaves,htree,hr,hroot,hsecond,hcbytes,hpayload,hpayload1,
          halpha,hfinal,hfbytes,hqueries,rfl⟩

theorem source (variant : transport.Variant) (hash : Hash)
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts)
    (p : prover.Publication)
    (h : prover.finish_opening variant hash prepared salts=ok (.Ok p)) :
    Trace hash prepared salts
      (prover.round (alloc.vec.Vec.deref prepared.q1) (alloc.vec.Vec.deref prepared.w1))
      (fun a => prover.fold (alloc.vec.Vec.deref prepared.q1) a false) p := by
  rw [PV_RunJoin_FinishContext47.source] at h
  exact run variant hash prepared salts _ _ p h
#print axioms run
#print axioms source
end R1Z.PV_RJQ_FinishTrace
