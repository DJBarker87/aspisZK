import R1Z.ProverCommitEncoderEval54
/-! All four 256-coefficient source channels, with canonical output and exact value. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderChannels54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitEncoderEval54

attribute [local irreducible] source value sourceArray

theorem collect_channel (f : Nat → Raw) (s : Usize) (hs : s.val<4) :
    ∃ v, encoder54.collect (Array.to_slice (sourceArray 1024#usize f))
      4#usize s 0#usize 256#usize (alloc.vec.Vec.new _)=ok v ∧
      v.val=List.ofFn (fun i : Fin 256 => source (f (4*i.val+s.val))) := by
  have hlen : (Array.to_slice (sourceArray 1024#usize f)).val.length=1024 := by
    simp only [Array.to_slice,sourceArray,List.length_ofFn];rfl
  obtain ⟨v,hv,hlist⟩ := ProverCommitEncoderCollect54.collect
    (Array.to_slice (sourceArray 1024#usize f)) 4#usize s 0#usize 256#usize 256 rfl
    (by decide) (by decide) hs
    (by intro k hk;rw [hlen];change 4*(0+k)+s.val<1024;omega)
    (alloc.vec.Vec.new _) (by decide)
  refine ⟨v,hv,?_⟩
  simpa only [alloc.vec.Vec.new,List.nil_append,Array.to_slice,sourceArray,List.getElem_ofFn,
    show (0#usize).val=0 from rfl,show (4#usize).val=4 from rfl,Nat.zero_add] using hlist


theorem channel_value (f : Nat → Raw) (hf : ∀ i, i<1024 → canonical (f i))
    (p : Nat → U32) (hp : ∀ i, i<9 → (p i).val<2147483647)
    (s : Usize) (hs : s.val<4) :
    ∃ v z, encoder54.collect (Array.to_slice (sourceArray 1024#usize f))
      4#usize s 0#usize 256#usize (alloc.vec.Vec.new _)=ok v ∧
      encoder54.eval_rec (alloc.vec.Vec.deref v) 0#usize 8#usize (nodes p)=ok (source z) ∧
      canonical z ∧ value z=eval 8 (fun i => value (f (4*i+s.val)))
        (fun i => value (base (p i))) 0 := by
  obtain ⟨v,hv,hlist⟩ := collect_channel f s hs
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitEncoderEval54.exact_result 8 (by decide)
    8#usize 0#usize rfl (by decide) (fun i => f (4*i+s.val))
    (by intro i hi;apply hf;change i<256 at hi;omega) (alloc.vec.Vec.deref v) hlist p hp
  exact ⟨v,z,hv,hz,hcz,hdz⟩

theorem exact_result (f : Nat → Raw) (hf : ∀ i, i<1024 → canonical (f i))
    (p : Nat → U32) (hp : ∀ i, i<9 → (p i).val<2147483647) :
    ∃ out : Nat → Raw,
      encoder54.channels (sourceArray 1024#usize f) (nodes p)=ok (sourceArray 4#usize out) ∧
      (∀ s, s<4 → canonical (out s)) ∧
      ∀ s : Fin 4, value (out s.val)=eval 8 (fun i => value (f (4*i+s.val)))
        (fun i => value (base (p i))) 0 := by
  obtain ⟨a,z0,ha,hz0,hc0,hd0⟩ := channel_value f hf p hp 0#usize (by decide)
  obtain ⟨b,z1,hb,hz1,hc1,hd1⟩ := channel_value f hf p hp 1#usize (by decide)
  obtain ⟨c,z2,hc,hz2,hc2,hd2⟩ := channel_value f hf p hp 2#usize (by decide)
  obtain ⟨d,z3,hd,hz3,hc3,hd3⟩ := channel_value f hf p hp 3#usize (by decide)
  let out : Nat → Raw := fun i => match i with | 0 => z0 | 1 => z1 | 2 => z2 | _ => z3
  refine ⟨out,?_,?_,?_⟩
  · simp only [encoder54.channels,lift,bind_tc_ok,ha,hb,hc,hd,hz0,hz1,hz2,hz3]
    unfold sourceArray
    rfl
  · intro s hs
    interval_cases s
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
  · intro s
    fin_cases s
    · exact hd0
    · exact hd1
    · exact hd2
    · exact hd3

#print axioms collect_channel
#print axioms channel_value
#print axioms exact_result
end R1Z.ProverCommitEncoderChannels54
