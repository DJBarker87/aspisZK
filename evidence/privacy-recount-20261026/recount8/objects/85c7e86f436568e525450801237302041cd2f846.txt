import R1Z.PV_RunJoin_SemanticStep40
import R1Z.PV_RunJoin_SemanticLengths40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticLoop40
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_SemanticDomain40
variable [ExternalTypes]

/-- Complete source loop on a byte-domain certificate, with all row helper
Results proved by the copy/compact laws and exact ordered output bytes. -/
theorem complete (ops : ExternalFuns) (logical : Slice U8) (count : U8)
    (at1 : Usize) (row : U8) (records : List (List U8))
    (domain : Domain ops logical count at1 row records) (out : alloc.vec.Vec U8)
    (room : out.length+records.flatten.length≤Usize.max) :
    ∃ next, @host_compact.compact_semantic_loop _ (ProverRwP6BodyCandidate.selected ops)
      logical out count at1 row=.ok (.Ok (),next) ∧
      next.val=out.val ++ records.flatten := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  induction domain generalizing out with
  | nil at1 row last cursor =>
    refine ⟨out,?_,by simp only [List.flatten_nil,List.append_nil]⟩
    unfold host_compact.compact_semantic_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_SemanticStep40.stop logical count row out at1 last cursor,bind_tc_ok]
  | copy at1 size row tag rest more shape small bound tail ih =>
    have available : out.length+(raw logical at1 size).length+rest.flatten.length≤Usize.max := by
      simpa only [List.flatten_cons,List.length_append,Nat.add_assoc] using room
    have wirelen := PV_RunJoin_SemanticLengths40.raw logical at1 size bound
    obtain ⟨mid,hm,hmid⟩ := PV_RunJoin_SemanticCopy40.row ops logical out row tag at1 size
      shape small bound (by rw [wirelen] at available;omega)
    have hbytes : mid.val=out.val ++ raw logical at1 size := by
      simpa only [raw,List.append_assoc] using hmid
    have midlen : mid.length=out.length+(raw logical at1 size).length := by
      change mid.val.length=out.val.length+_
      rw [hbytes,List.length_append]
    obtain ⟨next,hn,hval⟩ := ih mid (by rw [midlen];exact available)
    refine ⟨next,?_,?_⟩
    · unfold host_compact.compact_semantic_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [PV_RunJoin_SemanticStep40.next logical count out mid at1 (after at1 size) row more hm]
      simp only [bind_tc_ok]
      exact hn
    · rw [hval,hbytes,List.flatten_cons,List.append_assoc]
  | compact at1 size row tag n rest more shape large sizeval bound zero tail ih =>
    have available : out.length+(compact logical at1 size n).length+rest.flatten.length≤Usize.max := by
      simpa only [List.flatten_cons,List.length_append,Nat.add_assoc] using room
    have wirelen := PV_RunJoin_SemanticLengths40.compact logical at1 size n sizeval bound
    obtain ⟨mid,hm,hmid,hmlen⟩ := PV_RunJoin_SemanticCompact40.row ops logical out row tag at1 size n
      shape large sizeval bound (by rw [wirelen] at available;omega) zero
    have hbytes : mid.val=out.val ++ compact logical at1 size n := by
      simpa only [compact,List.append_assoc] using hmid
    have midlen : mid.length=out.length+(compact logical at1 size n).length := by
      rw [hmlen,wirelen]
      omega
    obtain ⟨next,hn,hval⟩ := ih mid (by rw [midlen];exact available)
    refine ⟨next,?_,?_⟩
    · unfold host_compact.compact_semantic_loop
      rw [ProverRw19LoopBind.loop_bind]
      dsimp only
      rw [PV_RunJoin_SemanticStep40.next logical count out mid at1 (after at1 size) row more hm]
      simp only [bind_tc_ok]
      exact hn
    · rw [hval,hbytes,List.flatten_cons,List.append_assoc]
#print axioms complete
end R1Z.PV_RunJoin_SemanticLoop40
