import LPq_OuterTrace
set_option autoImplicit false
namespace AspisR1.LPq_OuterConstruct
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort AspisR1CurrentPreparedClaim

theorem loop {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (k : LPq_WeightedStep.Seven)
    (hk : LPq_WeightedStep.canonical k)
    (domain : ∀ p : Usize, p.val<6 → LPq_PointConstruct.ReadDomain sem y1 g p)
    (fuel : Nat) (iter : LPq_OuterTrace.Range) (parts : LPq_WeightedStep.Seven)
    (hp : LPq_WeightedStep.canonical parts) (last : iter.end.val=6)
    (bound : iter.start.val≤6) (remaining : 6-iter.start.val≤fuel) :
    ∃ out, LPq_OuterTrace.Trace sem y1 g k iter parts out ∧ canonE out := by
  induction fuel generalizing iter parts with
  | zero =>
    have stopped : ¬ (iter.start.val < iter.end.val) := by omega
    obtain ⟨⟨o,iter'⟩,call,shape⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
        (by intros;rfl) (by intros;rfl) iter)
    simp only [stopped,↓reduceIte] at shape
    obtain ⟨out,sum,co,_⟩ := LPq_Weighted.source k parts hk hp
    exact ⟨out,.done iter iter' parts out (by rw [shape.1.1] at call;exact call) sum,co⟩
  | succ n ih =>
    obtain ⟨⟨o,iter'⟩,call,shape⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
        (by intros;rfl) (by intros;rfl) iter)
    by_cases active : iter.start.val < iter.end.val
    · simp only [active,↓reduceIte] at shape
      have hi : iter.start.val<6 := by omega
      obtain ⟨xs,value,dot⟩ := LPq_PointConstruct.from_zero sem y1 g iter.start (domain _ hi)
      obtain ⟨i,inc,vi⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x:=iter.start) (y:=1#usize) (by scalar_tac))
      have advance : i.val=iter.start.val+1 := by simpa only [UScalar.ofNatCore_val_eq] using vi
      have within : i.val<7 := by omega
      have ci := LPq_ArrayPorts.canonical_set parts i value hp (LPq_OutputDomains.point dot)
      have next : iter'.start.val=iter.start.val+1 := shape.1.2
      have last' : iter'.end.val=6 := by rw [shape.2];exact last
      obtain ⟨out,tail,co⟩ := ih iter' (parts.set i value) ci last' (by omega) (by omega)
      exact ⟨out,.step iter.start i value xs (by rw [shape.1.1] at call;exact call)
        dot inc within tail,co⟩
    · simp only [active,↓reduceIte] at shape
      obtain ⟨out,sum,co,_⟩ := LPq_Weighted.source k parts hk hp
      exact ⟨out,.done iter iter' parts out (by rw [shape.1.1] at call;exact call) sum,co⟩

#print axioms loop
end AspisR1.LPq_OuterConstruct
