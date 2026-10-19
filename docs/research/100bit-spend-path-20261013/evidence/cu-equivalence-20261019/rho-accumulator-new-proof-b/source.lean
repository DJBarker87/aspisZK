import AspisR1RhoAccumulatorNew.Funs
import CuSavingsRhoHeap
import CuSavingsRhoPowerTail

/-! Success invariants of the complete actual accumulator constructor.
Allocation is not assumed successful. Every successful constructor output has
the actual length, canonical initial power and zero counter, even for an
arbitrary reserve boundary. Canonicality of its weight contents is separate:
that needs the actual reserve frame, not merely its successful return. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoAccumulatorNew
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

def length (v : transport.Variant) : Usize :=
  match v with
  | .S1 => 256#usize
  | .S2 | .D => 64#usize

private theorem mul_eq (x y z : Usize) (h : x.val*y.val=z.val) :
    (x*y : Result Usize) = .ok z := by
  obtain ⟨out,hr,hv⟩ := ExtractedCurrentReducerOps.tryMk_success (ty:=.Usize)
    (x.val*y.val) (by rw [h];exact z.bv.isLt)
  change UScalar.mul x y = .ok out at hr
  exact hr.trans (congrArg Result.ok (UScalar.eq_of_val_eq (hv.trans h)))

private theorem shift_eq (x y z : Usize) (hy : y.val < UScalarTy.Usize.numBits)
    (h : x.val >>> y.val=z.val) : (x >>> y : Result Usize) = .ok z := by
  obtain ⟨out,hr,hv,_⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec x y hy)
  exact hr.trans (congrArg Result.ok (UScalar.eq_of_val_eq (hv.trans h)))

private theorem shift2 : (1024#usize >>> 2#usize : Result Usize) = .ok 256#usize := by
  apply shift_eq _ _ _ (by scalar_tac)
  have hx : (1024#usize).val=1024 := by scalar_tac
  have hy : (2#usize).val=2 := by scalar_tac
  have hz : (256#usize).val=256 := by scalar_tac
  rw [hx,hy,hz]
  decide

private theorem shift4 : (1024#usize >>> 4#usize : Result Usize) = .ok 64#usize := by
  apply shift_eq _ _ _ (by scalar_tac)
  have hx : (1024#usize).val=1024 := by scalar_tac
  have hy : (4#usize).val=4 := by scalar_tac
  have hz : (64#usize).val=64 := by scalar_tac
  rw [hx,hy,hz]
  decide

theorem final_len_success (v : transport.Variant) :
    transport.Variant.final_len v = .ok (length v) := by
  cases v <;>
    simp [transport.Variant.final_len,transport.Variant.folds,
      transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
      transport.Variant.read_discriminant,length]
  · rw [mul_eq 2#usize 1#usize 2#usize (by scalar_tac)]
    exact shift2
  · rw [mul_eq 2#usize 2#usize 4#usize (by scalar_tac)]
    exact shift4
  · rw [mul_eq 2#usize 2#usize 4#usize (by scalar_tac)]
    exact shift4

theorem length_bound (v : transport.Variant) : (length v).val ≤ 256 := by
  cases v <;> simp only [length] <;> scalar_tac

theorem one_canonical : CuSavingsRhoPowerTail.Canonical aspis_core.field.QM31.ONE := by
  rw [aspis_core.field.QM31.ONE]
  change ((1#u32).val < 2147483647 ∧ (0#u32).val < 2147483647) ∧
    ((0#u32).val < 2147483647 ∧ (0#u32).val < 2147483647)
  constructor <;> constructor <;> scalar_tac

def initialized (weights : alloc.vec.Vec aspis_core.field.QM31) : verifier.Accumulator :=
  {weights:=weights,rhs:=aspis_core.field.WideExact.ZERO,
   power:=aspis_core.field.QM31.ONE,next:=0#usize}

variable [AspisR1CuRho.HeapReserve]

/-- Complete constructor outcome; heap errors, runtime failures and divergence
are retained. The only successful branch is the actual source record. -/
theorem source_outcome (v : transport.Variant) :
    verifier.Accumulator.new v = (do
      let result ← aspis_core.r0.heap.filled
        aspis_core.field.QM31.Insts.CoreMarkerCopy (length v) aspis_core.field.QM31.ZERO
      match result with
      | .Err _ => .ok (.Err verifier.Error.Allocation)
      | .Ok weights => .ok (.Ok (initialized weights))) := by
  unfold verifier.Accumulator.new
  rw [final_len_success]
  simp only [bind_tc_ok]
  cases hheap : aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy
      (length v) aspis_core.field.QM31.ZERO with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

theorem source_success (v : transport.Variant) (out : verifier.Accumulator)
    (h : verifier.Accumulator.new v = .ok (.Ok out)) :
    out.power=aspis_core.field.QM31.ONE ∧ CuSavingsRhoPowerTail.Canonical out.power ∧
    out.next.val=0 ∧ out.weights.val.length=(length v).val ∧
    out.weights.val.length ≤ 256 ∧ out.rhs=aspis_core.field.WideExact.ZERO := by
  rw [source_outcome] at h
  obtain ⟨result,hheap,h⟩ := bind_ok _ _ _ h
  cases result with
  | Err error => cases h
  | Ok weights =>
    have heq : initialized weights=out := core.result.Result.Ok.inj (Result.ok.inj h)
    cases heq
    have hlen := CuSavingsRhoHeap.source_length
      aspis_core.field.QM31.Insts.CoreMarkerCopy (length v)
      aspis_core.field.QM31.ZERO weights hheap
    refine ⟨rfl,one_canonical,?_,hlen,?_,rfl⟩
    · change (0#usize).val=0
      scalar_tac
    · exact hlen ▸ length_bound v

#print axioms final_len_success
#print axioms length_bound
#print axioms one_canonical
#print axioms source_outcome
#print axioms source_success
end AspisR1.CuSavingsRhoAccumulatorNew
