import S9ActualPairRegularPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairQuotient64V1
abbrev Iter := core.ops.range.Range Usize

/-- Symbolic constant-shift law; no architecture modulus is evaluated. -/
theorem shift_two_val (x : Usize) :
    (Usize.wrapping_shr x 2#u32).val=x.val/4 := by
  have hbits : 2 < System.Platform.numBits := by
    have := System.Platform.le_numBits
    omega
  change (x.bv.ushiftRight ((2#u32).val % System.Platform.numBits)).toNat=x.val/4
  have htwo : (2#u32).val=2 := rfl
  rw [htwo,Nat.mod_eq_of_lt hbits]
  calc
    (x.bv.ushiftRight 2).toNat = x.bv.toNat >>> 2 :=
      BitVec.toNat_ushiftRight x.bv 2
    _ = x.val/4 := by simp only [UScalar.bv_toNat,Nat.shiftRight_eq_div_pow]

private theorem shift1024 : Usize.wrapping_shr 1024#usize 2#u32=256#usize := by
  apply UScalar.eq_of_val_eq
  rw [shift_two_val]
  rfl
private theorem shift256 : Usize.wrapping_shr 256#usize 2#u32=64#usize := by
  apply UScalar.eq_of_val_eq
  rw [shift_two_val]
  rfl

/-- The actual expected-length source loop makes exactly two successful
right-shift steps. Iterator specifications provide the control flow. -/
theorem expected_length_twofold :
    weights.Weights.pair_loop0 {start:=0#usize,«end»:=2#usize} 1024#usize=
      .ok (64#usize) := by
  let initial : Iter := {start:=0#usize,«end»:=2#usize}
  obtain ⟨p0,hn0,hp0⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) initial (by decide))
  rcases p0 with ⟨o0,it1⟩
  rcases hp0 with ⟨ho0,hs1,he1⟩
  subst o0
  have h1 : it1.start.val=1 := by simpa [initial] using hs1
  have he1' : it1.end=2#usize := he1
  have hlt1 : it1.start.val < it1.end.val := by rw [h1,he1']; decide
  obtain ⟨p1,hn1,hp1⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) it1 hlt1)
  rcases p1 with ⟨o1,it2⟩
  rcases hp1 with ⟨ho1,hs2,he2⟩
  subst o1
  have h2 : it2.start.val=2 := by rw [h1] at hs2; exact hs2
  have he2' : it2.end=2#usize := he2.trans he1'
  have hge2 : it2.start.val ≥ it2.end.val := by rw [h2,he2']; decide
  obtain ⟨p2,hn2,hp2⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros; rfl) it2 hge2)
  rcases p2 with ⟨o2,it3⟩
  rcases hp2 with ⟨ho2,he3⟩
  subst o2
  let step : Iter × Usize → Result (ControlFlow (Iter × Usize) Usize) :=
    fun s => weights.Weights.pair_loop0.body s.1 s.2
  change Aeneas.Std.loop step (initial,1024#usize)=.ok (64#usize)
  rw [Aeneas.Std.loop.eq_def]
  simp only [step,weights.Weights.pair_loop0.body,hn0,bind_tc_ok,lift,shift1024]
  change Aeneas.Std.loop step (it1,256#usize)=.ok (64#usize)
  rw [Aeneas.Std.loop.eq_def]
  simp only [step,weights.Weights.pair_loop0.body,hn1,bind_tc_ok,lift,shift256]
  change Aeneas.Std.loop step (it2,64#usize)=.ok (64#usize)
  rw [Aeneas.Std.loop.eq_def]
  simp only [step,weights.Weights.pair_loop0.body,hn2,bind_tc_ok]
  rfl

variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
theorem actual_pair_success_quotient64
    (self : weights.Weights) (alpha : Slice aspis_core.field.wide_exact.WideExact)
    (f : Slice U8) (kappa out : aspis_core.field.wide_exact.WideExact)
    (hfold : Slice.len alpha=2#usize)
    (h : weights.Weights.pair self alpha f kappa=.ok (.Ok out)) :
    (Slice.len f /32#usize : Result Usize)=.ok (64#usize) := by
  obtain ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
      hdiv,hexpected,hguard,_⟩ :=
    AspisR1S9ActualPairRegularPrefixV1.actual_pair_success_regular_prefix
      self alpha f kappa out hfold h
  have he : expectedN=64#usize := Result.ok.inj (hexpected.symm.trans expected_length_twofold)
  have hn : n=expectedN := bne_eq_false_iff_eq.mp hguard
  simpa only [hn,he] using hdiv

#print axioms shift_two_val
#print axioms expected_length_twofold
#print axioms actual_pair_success_quotient64
end AspisR1S9ActualPairQuotient64V1
