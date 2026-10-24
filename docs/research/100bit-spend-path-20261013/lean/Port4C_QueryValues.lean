import Port3_NativeQueryTerms
import CheckpointBytes5Output

/-! Invert the current release-MIR query at its actual opening, fold, geometry
and accumulation operands. No successful child is selected independently. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_QueryValues
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
abbrev M := aspis_core.field.M31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev K := aspis_core.field.QM31

private theorem guard {T : Type} (bad : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if bad then ok (.Err verifier.Error.Query) else tail)=ok (.Ok out)) :
    bad=false ∧ tail=ok (.Ok out) := by
  cases bad
  · exact ⟨rfl,h⟩
  · cases h

/-- All four physical accumulator fields, with the actual folded value. -/
theorem accumulated (ops : Ops) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (node : M) (value : E)
    (b bout : verifier.BatchedWeights)
    (h : verifier.accumulate_batched_with_node ops p a node value b=ok (out,bout)) :
    ∃ product,
      ops.op3 value a.power=ok product ∧ ops.op2 a.rhs product=ok out.rhs ∧
      ops.op9 a.power p.rho=ok out.power ∧ out.weights=a.weights ∧
      out.next=Usize.wrapping_add a.next 1#usize := by
  unfold verifier.accumulate_batched_with_node at h
  iterate 6 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨product,hprod,h⟩ := bind_success _ _ _ h
  obtain ⟨rhs,hrhs,h⟩ := bind_success _ _ _ h
  obtain ⟨trace,_,h⟩ := bind_success _ _ _ h
  obtain ⟨power,hpower,h⟩ := bind_success _ _ _ h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  cases Result.ok.inj h
  have hn := Result.ok.inj hn
  exact ⟨product,hprod,hrhs,hpower,rfl,hn.symm⟩

structure Observation (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) where
  query : U32
  opening : Slice U8
  dots : Array E 4#usize
  inverse : Array M 5#usize
  alpha0 : E
  alpha1 : E
  folded : E
  value : E
  values : Array E 4#usize
  selected : E
  u : Usize
  z : M
  square : M
  doubled : M
  one : M
  node : M
  query_read : Array.index_usize p.queries a.next=ok query
  cast : lift (UScalar.cast .Usize query)=ok u
  opening_read : ops.op11 proof a.next=ok opening
  dots_read : ops.op20 opening g=ok dots
  inverse_read : ops.op18 geometry a.next=ok inverse
  alpha0_read : Array.index_usize p.alpha 0#usize=ok alpha0
  circle : ops.op17 alpha0 dots inverse=ok folded
  values_read : ops.op0 4#usize
    (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops)
    opening=ok values
  selected_read : ∃ rem, u % 4#usize=ok rem ∧ Array.index_usize values rem=ok selected
  comparison : core.cmp.PartialEq.ne.trait_default ops.widePartialEq folded selected=ok false
  alpha1_read : Array.index_usize p.alpha 1#usize=ok alpha1
  line : ops.op16 alpha1 values inverse=ok value
  z_read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice M)
    geometry.line_z (Usize.wrapping_sub a.next geometry.start)=ok z
  square_call : ops.op7 z z=ok square
  double_call : ops.op8 square=ok doubled
  one_call : ops.op5=ok one
  node_call : ops.op6 doubled one=ok node
  accumulate : verifier.accumulate_batched_with_node ops p a node value b=ok (out,bout)
  marked : ops.op19 obs (verifier.Phase.Query a.next)=ok ()

theorem observed (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights)
    (h : verifier.candidate.query_values ops proof p a g obs geometry b=ok (.Ok (out,bout))) :
    Nonempty (Observation ops proof p a out g obs geometry b bout) := by
  unfold verifier.candidate.query_values at h
  obtain ⟨query,hq,h⟩ := bind_success _ _ _ h
  obtain ⟨u,hu,h⟩ := bind_success _ _ _ h
  obtain ⟨opening,ho,h⟩ := bind_success _ _ _ h
  obtain ⟨dots,hd,h⟩ := bind_success _ _ _ h
  iterate 15 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨inverse,hi,h⟩ := bind_success _ _ _ h
  obtain ⟨alpha0,ha0,h⟩ := bind_success _ _ _ h
  obtain ⟨folded,hcircle,h⟩ := bind_success _ _ _ h
  iterate 2 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨values,hvalues,h⟩ := bind_success _ _ _ h
  obtain ⟨rem,hrem,h⟩ := bind_success _ _ _ h
  obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
  obtain ⟨bad,hbad,h⟩ := bind_success _ _ _ h
  obtain ⟨rfl,h⟩ := guard _ _ _ h
  obtain ⟨alpha1,ha1,h⟩ := bind_success _ _ _ h
  obtain ⟨value,hline,h⟩ := bind_success _ _ _ h
  iterate 3 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨offset,hoff,h⟩ := bind_success _ _ _ h
  obtain ⟨z,hz,h⟩ := bind_success _ _ _ h
  obtain ⟨square,hsq,h⟩ := bind_success _ _ _ h
  obtain ⟨doubled,hdbl,h⟩ := bind_success _ _ _ h
  obtain ⟨one,hone,h⟩ := bind_success _ _ _ h
  obtain ⟨node,hnode,h⟩ := bind_success _ _ _ h
  obtain ⟨pair,hacc,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨a1,b1⟩
  obtain ⟨marked,hmark,h⟩ := bind_success _ _ _ h
  cases marked
  cases Result.ok.inj h
  have he := Result.ok.inj hoff
  subst offset
  exact ⟨⟨query,opening,dots,inverse,alpha0,alpha1,folded,value,values,selected,u,
    z,square,doubled,one,node,hq,hu,ho,hd,hi,ha0,hcircle,hvalues,
    ⟨rem,hrem,hselected⟩,hbad,ha1,hline,hz,hsq,hdbl,hone,hnode,hacc,hmark⟩⟩

#print axioms accumulated
#print axioms observed
end AspisR1.Port4C_QueryValues
end
