import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_CellUnique
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
theorem source (x y : FIo_Install.NE)
    (h : ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs x) j).val=
      (cell (JFv_TX2_FromLimbsMeaning.limbs y) j).val) : x=y := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h0⟩⟩⟩
  rcases y with ⟨⟨⟨a1,b1⟩,⟨c1,d1⟩⟩,⟨⟨e1,f1⟩,⟨g1,h1⟩⟩⟩
  congr 3
  · exact UScalar.eq_of_val_eq (h 0)
  · exact UScalar.eq_of_val_eq (h 1)
  · exact UScalar.eq_of_val_eq (h 2)
  · exact UScalar.eq_of_val_eq (h 3)
  · exact UScalar.eq_of_val_eq (h 4)
  · exact UScalar.eq_of_val_eq (h 5)
  · exact UScalar.eq_of_val_eq (h 6)
  · exact UScalar.eq_of_val_eq (h 7)
#print axioms source
end AspisR1.JFw_TX2_CellUnique
end
