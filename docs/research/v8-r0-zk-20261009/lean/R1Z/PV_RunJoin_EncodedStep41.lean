import R1Z.PV_RunJoin_OpeningCell41
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncodedStep41
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

def zero : W := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def at (values : Slice W) (i : Nat) : W := values.val[i]?.getD zero

theorem read (values : Slice W) (i : Usize) (hi : i.val<values.length) :
    Slice.index_usize values i=.ok (at values i.val) := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq,List.getElem?_eq_getElem hi,at]
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem stop (ops : ExternalFuns) (values : Slice W) (out : alloc.vec.Vec U8)
    (i : Usize) (hi : values.length≤ i.val) :
    @prover.encoded_slice_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      values out i=.ok (.done out) := by
  simp only [prover.encoded_slice_loop.body,
    show ¬i<Slice.len values from (by change ¬i.val<values.length;omega),↓reduceIte]

theorem step (ops : ExternalFuns) (values : Slice W) (out : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val<values.length) (room : out.length+32≤Usize.max) :
    ∃ next, @prover.encoded_slice_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      values out i=.ok (.cont (next,Usize.wrapping_add i 1#usize)) ∧
      next.val=out.val ++ (PV_RunJoin_FlatBytes35.wire (at values i.val)).val := by
  let w := at values i.val
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_ByteAppend38.append out
    (Array.to_slice (PV_RunJoin_FlatBytes35.wire w)) room
  refine ⟨next,?_,hv⟩
  unfold prover.encoded_slice_loop.body
  simp only [show i<Slice.len values from hi,↓reduceIte]
  rw [read values i hi]
  simp only [bind_tc_ok]
  rw [show @aspis_core.field.wide_exact.WideExact.to_le_bytes _
    (ProverRwP6BodyCandidate.selected ops) w=.ok (PV_RunJoin_FlatBytes35.wire w)
    from PV_RunJoin_FlatBytes35.installed ops w]
  simp only [bind_tc_ok,lift,hn]
#print axioms read
#print axioms stop
#print axioms step
end R1Z.PV_RunJoin_EncodedStep41
