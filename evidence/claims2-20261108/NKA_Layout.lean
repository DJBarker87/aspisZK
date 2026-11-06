import NKA_InitializedPrefix
set_option autoImplicit false
namespace AspisR1.NKA_Layout

def column (i : Fin 116) : Fin 29 := ⟨i.val/4,by omega⟩
def limb (i : Fin 116) : Fin 4 := ⟨i.val%4,by omega⟩

/-- Converts every native p/column/limb observation into the exact initialized
prefix coordinate. Both directions are covered; no selected word is omitted. -/
theorem offset (p : Fin 3) (i : Fin 116) :
 4*(29*p.val+(column i).val)+(limb i).val=116*p.val+i.val := by
 simp only [column,limb]
 omega

theorem bounded (p : Fin 3) (i : Fin 116) : 116*p.val+i.val<348 := by omega

def flatten (k : Fin 29) (l : Fin 4) : Fin 116 := ⟨4*k.val+l.val,by omega⟩

theorem coordinates (k : Fin 29) (l : Fin 4) :
 column (flatten k l)=k ∧ limb (flatten k l)=l := by
 constructor <;> apply Fin.ext <;> simp only [column,limb,flatten] <;> omega

theorem complete (i : Fin 116) : flatten (column i) (limb i)=i := by
 apply Fin.ext
 simp only [column,limb,flatten]
 omega

theorem request : 1392=3*29*4*4 := by decide

#print axioms offset
#print axioms bounded
#print axioms coordinates
#print axioms complete
#print axioms request
end AspisR1.NKA_Layout
