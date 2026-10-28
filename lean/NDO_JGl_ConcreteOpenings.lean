import NDO_JGl_NumericData
import NDO_JGl_GatherMore
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_ConcreteOpenings
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (cells canonical)
open JGl_GatherValue
theorem a (out : State) (hc : canonical JGl_ConcreteSelected.data)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy f0 field.QM31.ZERO JGl_ConcreteSelected.data=ok out) :
    out=JGl_NumericData.a := by
  have v := JGl_GatherValue.zero JGl_ConcreteSelected.data out hc run
  have concrete (i : Fin (16#usize).val) :
      cells JGl_ConcreteSelected.data ⟨0+i.val,by have h:=i.isLt;change i.val<16 at h;change 0+i.val<84;omega⟩=
        cells JGl_NumericData.a i := by
    fin_cases i <;> rfl
  simp only [Nat.zero_add] at concrete
  apply Subtype.ext
  apply List.ext_getElem
  · exact out.property.trans JGl_NumericData.a.property.symm
  · intro n hn hd
    have hi : n<(16#usize).val := by simpa only [out.property] using hn
    exact (v ⟨n,hi⟩).trans (concrete ⟨n,hi⟩)
#print axioms a
theorem b (out : State) (hc : canonical JGl_ConcreteSelected.data)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy f1 field.QM31.ZERO JGl_ConcreteSelected.data=ok out) :
    out=JGl_NumericData.b := by
  have v := JGl_GatherMore.one JGl_ConcreteSelected.data out hc run
  have concrete (i : Fin (16#usize).val) :
      cells JGl_ConcreteSelected.data ⟨28+i.val,by have h:=i.isLt;change i.val<16 at h;change 28+i.val<84;omega⟩=
        cells JGl_NumericData.b i := by
    fin_cases i <;> rfl
  apply Subtype.ext
  apply List.ext_getElem
  · exact out.property.trans JGl_NumericData.b.property.symm
  · intro n hn hd
    have hi : n<(16#usize).val := by simpa only [out.property] using hn
    exact (v ⟨n,hi⟩).trans (concrete ⟨n,hi⟩)
#print axioms b
theorem c (out : State) (hc : canonical JGl_ConcreteSelected.data)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy f2 field.QM31.ZERO JGl_ConcreteSelected.data=ok out) :
    out=JGl_NumericData.c := by
  have v := JGl_GatherMore.two JGl_ConcreteSelected.data out hc run
  have concrete (i : Fin (16#usize).val) :
      cells JGl_ConcreteSelected.data ⟨56+i.val,by have h:=i.isLt;change i.val<16 at h;change 56+i.val<84;omega⟩=
        cells JGl_NumericData.c i := by
    fin_cases i <;> rfl
  apply Subtype.ext
  apply List.ext_getElem
  · exact out.property.trans JGl_NumericData.c.property.symm
  · intro n hn hd
    have hi : n<(16#usize).val := by simpa only [out.property] using hn
    exact (v ⟨n,hi⟩).trans (concrete ⟨n,hi⟩)
#print axioms c
end AspisR1.JGl_ConcreteOpenings
end
