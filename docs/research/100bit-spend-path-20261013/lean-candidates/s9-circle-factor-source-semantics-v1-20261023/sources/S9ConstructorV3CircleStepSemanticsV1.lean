import S9CircleFactorModelV1
import S9ConstructorV3CircleCellSemanticsV1
import S9ConstructorTensorFactorMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3CircleStepSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1
open AspisR1S9FactorArrayEntryV1 AspisR1S9FactorTableSemanticsV1
open AspisR1S9CircleFactorModelV1 AspisCircleTensorBinding

private theorem row_index_value (k : Usize) (hk : k.val<2) :
    (Usize.wrapping_add 3#usize k).val = 3+k.val := by
  have h4 : (4#usize).val = 4 := rfl
  have hsize : 4 < UScalar.size .Usize := by
    simpa only [UScalar.size,h4] using (4#usize).hBounds
  rw [Usize.wrapping_add_val_eq]
  change (3+k.val) % UScalar.size .Usize = 3+k.val
  exact Nat.mod_eq_of_lt (by omega)

private theorem make4_circle_meaning
    (original : ExactQM) (d : Nat) (x y q : Q)
    (hx : decode x = base original d)
    (hy : decode y = doubledFactor (decode x) 1)
    (hq : decode q = decode x*decode y) :
    ∀ (i : Usize) (hi : i.val<4),
      decode (atN (Array.make 4#usize
        [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,x,y,q] : Cell) i hi) =
      coefficient original d i.val := by
  have hyy : decode y = doubledFactor (base original d) 1 := by rw [hy,hx]
  intro i hi
  have hcases : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have he : i=0#usize := UScalar.eq_of_val_eq h0
    subst i
    change decode AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE = 1
    exact AspisR1S9ConstructorTensorFactorMapV1.ctor_one_decode
  · have he : i=1#usize := UScalar.eq_of_val_eq h1
    subst i
    change decode x = base original d
    exact hx
  · have he : i=2#usize := UScalar.eq_of_val_eq h2
    subst i
    change decode y = doubledFactor (base original d) 1
    exact hyy
  · have he : i=3#usize := UScalar.eq_of_val_eq h3
    subst i
    change decode q = base original d * doubledFactor (base original d) 1
    rw [hq,hx,hyy]

/-- One accepted actual circle-factor iteration advances the retained
natural-circle recurrence and the complete decoded table invariant. The
exact write, source arithmetic and untouched entries all come from that
same body execution. -/
theorem circle_body_success_model_step
    (before : Table) (original : ExactQM) (k : Usize)
    (iter iterNext : R) (factors factorsOut : Factors) (x xNext : Q)
    (hk : k.val<2) (hend : iter.end=5#usize) (hstart : 1≤iter.start.val)
    (hx : Can x) (hxm : decode x = base original iter.start.val)
    (hm : Meaning factors (prefixTable before (3+k.val) 1 iter.start.val original))
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.cont (iterNext,factorsOut,xNext))) :
    iterNext.start.val=iter.start.val+1 ∧ iterNext.end=5#usize ∧ Can xNext ∧
    decode xNext=base original iterNext.start.val ∧
    Meaning factorsOut (prefixTable before (3+k.val) 1 iterNext.start.val original) := by
  obtain ⟨d,y,q,i,old,back,rowOut,hnext,hi,hmut,hrow,hout,hyc,hqc,hxc,hyd,hqd,hxd⟩ :=
    AspisR1S9ConstructorV3CircleCellSemanticsV1.circle_cell_body_success_semantics
      k iter iterNext factors factorsOut x xNext hx hbody
  obtain ⟨hlt,hd,hs,he⟩ := next_some_progress iter iterNext d hnext
  have hdval : d.val=iter.start.val := congrArg UScalar.val hd
  have hdb : d.val<5 := by
    rw [hend] at hlt
    change iter.start.val<5 at hlt
    omega
  have hib := index_mut_bound factors i old back hmut
  change Result.ok (Usize.wrapping_add 3#usize k) = Result.ok i at hi
  have hie := Result.ok.inj hi
  have hiv : i.val=3+k.val := by rw [←hie,row_index_value k hk]
  have hym : decode y = doubledFactor (decode x) 1 :=
    hyd.trans (AspisR1S9ConstructorV3DoubleRetainedModelV1.double_expr_eq_retained_model (decode x))
  have hxn : decode xNext = doubledFactor (decode y) 1 :=
    hxd.trans (AspisR1S9ConstructorV3DoubleRetainedModelV1.double_expr_eq_retained_model (decode y))
  have hxnext : decode xNext=base original (iter.start.val+1) := by
    rw [hxn,hym]
    rw [←AspisV5FriNaturalBasisRadix4.doubledFactor_add,hxm]
    exact base_step_two original iter.start.val hstart
  have hc := make4_circle_meaning original iter.start.val x y q hxm hym hqd
  have hmeaning := accepted_write_meaning factors
    (prefixTable before (3+k.val) 1 iter.start.val original) i d old rowOut back
    (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,x,y,q] : Cell)
    (coefficient original iter.start.val) hib hdb hm hc hmut hrow
  rw [hiv,hdval,prefix_step before (3+k.val) 1 iter.start.val original hstart] at hmeaning
  rw [←hout] at hmeaning
  refine ⟨hs,he.trans hend,hxc,?_,?_⟩
  · rw [hs]
    exact hxnext
  · simpa only [hs] using hmeaning

#print axioms row_index_value
#print axioms make4_circle_meaning
#print axioms circle_body_success_model_step
end AspisR1S9ConstructorV3CircleStepSemanticsV1
