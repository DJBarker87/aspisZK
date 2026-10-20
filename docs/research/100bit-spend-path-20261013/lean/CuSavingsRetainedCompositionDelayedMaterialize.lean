import CuSavingsRetainedCompositionDelayedArrays
import CuSavingsArrayBuilderBounded
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionDelayedMaterialize
open Aeneas Aeneas.Std Result
open AspisR1RetainedDots AspisV8R17.RawReducer
open CuSavingsRetainedCompositionDelayedArrays CuSavingsRetainedCompositionDelayedScalar CuSavingsArrayBuilder

def word (x : U64) : U32 := UScalar.ofNatCore (x.val%P) (by
  have h := Nat.mod_lt x.val (show 0 < P by decide)
  change x.val%P < 4294967296
  change x.val%P < 2147483647 at h
  omega)

theorem reduce_word (x : U64) : field.M31.reduce_u64 x = .ok (word x) := by
  obtain ⟨z,hz,hv,_⟩ := reducer_mod x
  have he : z = word x := UScalar.eq_of_val_eq hv
  simpa only [he] using hz

def array (raw : Raw) : Canon :=
  ⟨raw.val.map word,by simpa only [List.length_map] using raw.property⟩

theorem array_read (raw : Raw) (i : Fin 8) : wordAt (array raw) i = word (wordAt raw i) := by
  simp only [wordAt,array,List.getElem_map]

theorem array_eq (old : Canon) (raw : Raw)
    (h : ∀ j : Fin 8, (wordAt old j).val = (wordAt raw j).val%P) : array raw = old := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [array,List.length_map];rw [raw.property,old.property]
  · intro j hj hk
    have hi : j < 8 := by simpa only [array,List.length_map,raw.property,show (8#usize).val=8 by scalar_tac] using hj
    apply UScalar.eq_of_val_eq
    simpa only [array,wordAt,List.getElem_map,word,UScalar.ofNatCore_val_eq] using (h ⟨j,hi⟩).symm

theorem callbacks (raw : Raw) (i : Usize) (hi : i.val < 8) :
    remap (fun (v,state) => (v,array state))
      (new_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut raw i) =
    old_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut (array raw) i := by
  simp only [new_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut,
    old_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut,
    read raw i hi,read (array raw) i hi,reduce_word,bind_tc_ok,array_read]
  rfl

theorem source_eq (old : Canon) (raw : Raw)
    (h : ∀ j : Fin 8, (wordAt old j).val = (wordAt raw j).val%P) :
    core.array.from_fn 8#usize
      new_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 raw =
    core.array.from_fn 8#usize
      old_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 old := by
  rw [←array_eq old raw h]
  apply CuSavingsArrayBuilderBounded.build_naturality _ _ array (fun _ => True)
  · intro state index _ hindex
    exact callbacks state index (by simpa only [show (8#usize).val=8 by scalar_tac] using hindex)
  · intros;trivial
  · trivial

#print axioms reduce_word
#print axioms array_eq
#print axioms callbacks
#print axioms source_eq
end AspisR1.CuSavingsRetainedCompositionDelayedMaterialize
