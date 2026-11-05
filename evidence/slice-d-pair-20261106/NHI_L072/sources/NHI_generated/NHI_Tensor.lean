import NHI_TensorExactOuter
import NHI_FactoredProducers
set_option autoImplicit false
noncomputable section
namespace NHI_Tensor
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHI_TensorExactOuter
abbrev W := FIo_Native.weights.Weights
abbrev Iter := core.ops.range.Range Usize
abbrev State := Iter × W × Slice NQ × Usize

def body (k : Usize) (t : State) :=
 FIo_Native.weights.Weights.tensor_loop0.body k t.1 t.2.1 t.2.2.1 t.2.2.2

def Domain (w : W) (k : Usize) (hk : k.val<5) : Prop :=
 ∀ d (hd : d.val<5),2 ≤ d.val → NHI_CellCanon.array (NHI_TensorExactCell.rowAt w k d hk hd)

def reference (w : W) (k : Usize) (hk : k.val<5) (input : Slice NQ) : Slice NQ :=
 let seed := NHI_SliceCells.put input 0 FIo_Native.aspis_core.field.QM31.ONE
 let a := expand w k 2#usize hk (by decide) 1#usize seed
 let b := expand w k 3#usize hk (by decide) 4#usize a
 expand w k 4#usize hk (by decide) 16#usize b

/-- Exact three-stage S2 tensor Result with four symbolic products per cell,
reverse original-cell reads, source seed and width progression 1,4,16. -/
theorem cohort (w : W) (k : Usize) (hk : k.val<5) (hf : Domain w k hk)
 (input : Slice NQ) (len : input.val.length=64) (ca : NHI_CellCanon.slice input) :
 FIo_Native.weights.Weights.tensor w k 2#usize input=ok (reference w k hk input) ∧
 NHI_CellCanon.slice (reference w k hk input) ∧ (reference w k hk input).val.length=64 := by
 let seed := NHI_SliceCells.put input 0 FIo_Native.aspis_core.field.QM31.ONE
 have seedRun := NHI_SliceCells.update input 0#usize (by change 0 < input.val.length;omega)
  FIo_Native.aspis_core.field.QM31.ONE
 have cs : NHI_CellCanon.slice seed := NHI_CellCanon.put input 0 _ ca NHI_FactoredProducers.one_canonical
 have ls : seed.val.length=64 := (NHI_SliceCells.length input 0 _).trans len
 let a := expand w k 2#usize hk (by decide) 1#usize seed
 obtain ⟨h2,c2,l2⟩ := active w k 2#usize 3#usize 1#usize hk (by decide) (by decide)
  (Or.inl rfl) (hf 2#usize (by decide) (by decide)) seed ls cs
 let b := expand w k 3#usize hk (by decide) 4#usize a
 obtain ⟨h3,c3,l3⟩ := active w k 3#usize 4#usize 4#usize hk (by decide) (by decide)
  (Or.inr (Or.inl rfl)) (hf 3#usize (by decide) (by decide)) a l2 c2
 let out := expand w k 4#usize hk (by decide) 16#usize b
 obtain ⟨h4,c4,l4⟩ := active w k 4#usize 5#usize 16#usize hk (by decide) (by decide)
  (Or.inr (Or.inr rfl)) (hf 4#usize (by decide) (by decide)) b l3 c3
 have step2 : body k ({start:=2#usize,«end»:=5#usize},w,seed,1#usize)=
  ok (cont ({start:=3#usize,«end»:=5#usize},w,a,4#usize)) := h2
 have step3 : body k ({start:=3#usize,«end»:=5#usize},w,a,4#usize)=
  ok (cont ({start:=4#usize,«end»:=5#usize},w,b,16#usize)) := h3
 have step4 : body k ({start:=4#usize,«end»:=5#usize},w,b,16#usize)=
  ok (cont ({start:=5#usize,«end»:=5#usize},w,out,64#usize)) := h4
 have stop : body k ({start:=5#usize,«end»:=5#usize},w,out,64#usize)=ok (done out) :=
  NHI_TensorOuterStep.done w k 64#usize {start:=5#usize,«end»:=5#usize} (by decide) out
 have run : loop (body k) ({start:=2#usize,«end»:=5#usize},w,seed,1#usize)=ok out := by
  rw [loop.eq_def,step2]
  simp only [bind_tc_ok]
  rw [loop.eq_def,step3]
  simp only [bind_tc_ok]
  rw [loop.eq_def,step4]
  simp only [bind_tc_ok]
  rw [loop.eq_def,stop]
 refine ⟨?_,c4,l4⟩
 unfold FIo_Native.weights.Weights.tensor
 rw [seedRun,bind_tc_ok]
 exact run

#print axioms cohort
end NHI_Tensor
end
