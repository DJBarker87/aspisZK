import R1Z.PV_RunJoin_SemanticLoopBound62
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticBound62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem encode (logical : Slice U8) (out : alloc.vec.Vec U8)
    (layout : compact.LOGICAL_SEMANTIC=ok 13831#usize)
    (room : out.length+55*13831≤Usize.max) :
    Post (fun pair => pair.2.length≤out.length+55*13831)
      (host_compact.compact_semantic logical out) := by
  unfold host_compact.compact_semantic
  rw [layout]
  simp only [bind_tc_ok]
  split
  · change out.length≤out.length+55*13831
    omega
  · rename_i good
    have length : logical.length=13831 := by
      have h : Slice.len logical=13831#usize := by
        simpa only [bne_iff_ne,ne_eq,not_not] using good
      exact congrArg UScalar.val h
    apply PV_RunJoin_PostBind62.bind _ _ _ _ (PV_RunJoin_SliceBound62.rangeTo logical 32#usize)
    intro prefix prefixBound
    apply PV_RunJoin_PostBind62.bind _ _ _ _ (PV_RunJoin_SliceBound62.append out prefix)
    intro mid midLength
    have rank : (0#u8).val+27=compact.SEMANTIC_ROWS.val := by
      unfold compact.SEMANTIC_ROWS
      rfl
    have h := PV_RunJoin_SemanticLoopBound62.loop logical 13831 (by omega)
      27 compact.SEMANTIC_ROWS 0#u8 mid 32#usize rank (by omega)
    cases he : host_compact.compact_semantic_loop logical mid compact.SEMANTIC_ROWS 32#usize 0#u8 with
    | fail e => trivial
    | div => trivial
    | ok pair =>
      rw [he] at h
      change pair.2.length≤out.length+55*13831
      change pair.2.length≤mid.length+2*13831*27 at h
      omega

#print axioms encode
end R1Z.PV_RunJoin_SemanticBound62
