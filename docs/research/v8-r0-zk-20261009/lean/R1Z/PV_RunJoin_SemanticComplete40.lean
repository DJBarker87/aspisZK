import R1Z.PV_RunJoin_SemanticLoop40
import R1Z.PV_RunJoin_BytePrefix40
import R1Z.ProverRwDictionaryLayoutValues
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticComplete40
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_SemanticDomain40
variable [ExternalTypes]

/-- The whole current emitted compact_semantic Result and exact ordered
payload on its source byte domain. Caller/model association of this byte
domain remains separate; no successful codec call is a premise. -/
theorem encode (ops : ExternalFuns) (logical : Slice U8) (out : alloc.vec.Vec U8)
    (records : List (List U8)) (length : logical.length=13831)
    (domain : Domain ops logical 27#u8 32#usize 0#u8 records)
    (room : out.length+32+records.flatten.length≤Usize.max) :
    ∃ next, @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops)
      logical out=.ok (.Ok (),next) ∧
      next.val=out.val ++ logical.val.take 32 ++ records.flatten := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  have layout : compact.LOGICAL_SEMANTIC=.ok 13831#usize :=
    ProverRwDictionaryLayoutValues.logical_semantic ops
  have lenword : Slice.len logical=13831#usize := by
    apply UScalar.eq_of_val_eq
    exact length
  obtain ⟨s,mid,hs,hm,hmid⟩ := PV_RunJoin_BytePrefix40.append logical out 32#usize
    (by change 32≤logical.length;omega) (by change out.length+32≤Usize.max;omega)
  have val32 : (32#usize).val=32 := by scalar_tac
  rw [val32] at hmid
  have midlen : mid.length=out.length+32 := by
    change mid.val.length=out.val.length+32
    rw [hmid,List.length_append,List.length_take]
    have hl : logical.val.length=13831 := length
    omega
  obtain ⟨next,hn,hnext⟩ := PV_RunJoin_SemanticLoop40.complete ops logical 27#u8
    32#usize 0#u8 records domain mid (by rw [midlen];exact room)
  refine ⟨next,?_,by rw [hnext,hmid];simp only [List.append_assoc]⟩
  simp only [host_compact.compact_semantic,layout,lenword,bind_tc_ok,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte,hs,hm,compact.SEMANTIC_ROWS,hn]
#print axioms encode
end R1Z.PV_RunJoin_SemanticComplete40
