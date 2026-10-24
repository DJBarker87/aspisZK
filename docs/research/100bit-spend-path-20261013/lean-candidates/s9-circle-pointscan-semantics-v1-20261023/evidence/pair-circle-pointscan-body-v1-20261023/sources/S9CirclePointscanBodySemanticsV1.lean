import S9CirclePointscanModelV1
import S9ConstructorV3PointScanBodyCanonicalV1
import S9ConstructorV3CircleLoopSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9CirclePointscanBodySemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1
open AspisR1S9FactorArrayEntryV1 AspisR1S9FactorTableSemanticsV1
open AspisR1S9CirclePointscanModelV1

private theorem row_index_value (k : Usize) (hk : k.val<2) :
    (Usize.wrapping_add 3#usize k).val=3+k.val := by
  have h4 : (4#usize).val=4 := rfl
  have hsize : 4 < UScalar.size .Usize := by
    simpa only [UScalar.size,h4] using (4#usize).hBounds
  rw [Usize.wrapping_add_val_eq]
  change (3+k.val)%UScalar.size .Usize=3+k.val
  exact Nat.mod_eq_of_lt (by omega)

private theorem zero_cell_meaning (point : Point) (q : Q)
    (hq : decode q=decode point.x*decode point.y) :
    ∀ (i : Usize) (hi : i.val<4),
      decode (atN (Array.make 4#usize
        [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,point.y,point.x,q] : Cell) i hi)=
        rowZero point i.val := by
  intro i hi
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases hc with h0|h1|h2|h3
  · have he : i=0#usize := UScalar.eq_of_val_eq h0
    subst i
    change decode AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE=1
    exact AspisR1S9ConstructorTensorFactorMapV1.ctor_one_decode
  · have he : i=1#usize := UScalar.eq_of_val_eq h1
    subst i
    rfl
  · have he : i=2#usize := UScalar.eq_of_val_eq h2
    subst i
    rfl
  · have he : i=3#usize := UScalar.eq_of_val_eq h3
    subst i
    exact hq

/-- One accepted actual outer pointscan body derives its arithmetic and inner
loop executions from that same body, and writes the full circle row. -/
theorem pointscan_body_success_meaning
    (before : Table) (z : Array Point 2#usize) (iter iterNext : R)
    (factors out : Factors)
    (hz : AspisR1S9ConstructorV3PointScanBodyCanonicalV1.PointsCanonical z)
    (hend : iter.end=2#usize)
    (hm : Meaning factors (circleScanTable before z iter.start.val))
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body z iter factors=
      .ok (.cont (iterNext,out))) :
    iterNext.start.val=iter.start.val+1 ∧ iterNext.end=2#usize ∧
      Meaning out (circleScanTable before z iterNext.start.val) := by
  obtain ⟨k,point,q,i,old,back,rowOut,x,hnext,hpoint,hq,hi,hmut,hrow,hx,hinner⟩ :=
    AspisR1S9ConstructorV3PointScanBodyCanonicalV1.pointscan_body_success_has_execution
      z iter iterNext factors out hbody
  obtain ⟨hlt,hk,hs,he⟩ := next_some_progress iter iterNext k hnext
  have hkb : k.val<2 := by
    rw [hend] at hlt
    change iter.start.val<2 at hlt
    have hv : k.val=iter.start.val := congrArg UScalar.val hk
    omega
  obtain ⟨hpx,hpy⟩ := hz k point hpoint
  obtain ⟨hqc,hqd⟩ := generated_mul_success_exact point.x point.y q hpx hpy hq
  obtain ⟨hxc,hxd⟩ :=
    AspisR1S9ConstructorV3DoubleRetainedModelV1.generated_double_success_model
      point.x x hpx hx
  have hxm : decode x=AspisR1S9CircleFactorModelV1.base (decode point.x) 1 := by
    simpa only [AspisR1S9CircleFactorModelV1.base] using hxd
  have hib := index_mut_bound factors i old back hmut
  change Result.ok (Usize.wrapping_add 3#usize k)=Result.ok i at hi
  have hie := Result.ok.inj hi
  have hiv : i.val=3+k.val := by rw [←hie,row_index_value k hkb]
  have hzero : (0#usize).val<5 := by decide
  have hwrite := accepted_write_meaning factors
    (circleScanTable before z iter.start.val) i 0#usize old rowOut back
    (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,
      point.y,point.x,q] : Cell) (rowZero point) hib hzero hm
    (zero_cell_meaning point q hqd) hmut hrow
  have hinnerM := AspisR1S9ConstructorV3CircleLoopSemanticsV1.circle_inner_success_meaning
    (write (circleScanTable before z iter.start.val) i.val 0 (rowZero point))
    (decode point.x) k (back rowOut) out x hkb hxc hxm hwrite hinner
  have hkval : k.val=iter.start.val := congrArg UScalar.val hk
  have hlookup : z.val[k.val]?=some point := by
    have heq := accepted_index_eq_atN z k hkb point hpoint
    rw [heq]
    unfold atN
    exact List.getElem?_eq_getElem (by simpa [z.property] using hkb)
  rw [hiv, AspisR1S9CirclePointscanModelV1.inner_prefix_row] at hinnerM
  rw [hkval] at hinnerM hlookup
  rw [circleScan_step before z iter.start.val point hlookup] at hinnerM
  refine ⟨hs,he.trans hend,?_⟩
  simpa only [hs] using hinnerM

#print axioms zero_cell_meaning
#print axioms pointscan_body_success_meaning
end AspisR1S9CirclePointscanBodySemanticsV1
