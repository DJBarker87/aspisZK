import NJB_PackLinearity
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_PackSum
open FIv_NativeValue (K)
/-- Packing commutes with a finite sum of arbitrary field vectors; no concrete
20level arithmetic is normalized. -/
theorem source {α : Type} (is : List α) (f : α → Fin 4 → K) :
 NJB_PackLinearity.pack (fun j=>(is.map (fun i=>f i j)).sum)=(is.map (fun i=>NJB_PackLinearity.pack (f i))).sum := by
 induction is with
 | nil=>simp only [List.map_nil,List.sum_nil,NJB_PackLinearity.zero]
 | cons i is ih=>
  simp only [List.map_cons,List.sum_cons]
  rw [NJB_PackLinearity.add,ih]
#print axioms source
end AspisR1.NKI_PackSum
end
