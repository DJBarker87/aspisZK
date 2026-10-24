import Port6CK_ScalarRoundtrip
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_ArrayRoundtrip
open Aeneas Aeneas.Std AspisR1Stage2
open CheckpointBytes3Namespaces CheckpointBytes4ReaderFields
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec

theorem k (xs : List aspis_core.field.QM31) (n : Nat) (length : xs.length=n)
    (canonical : ∀ j : Fin n, Canonical (toK (xs[j.val]'(by omega)))) :
    xs=(List.ofFn (fun j : Fin n => exactK (toK (xs[j.val]'(by omega))) (canonical j))).map sourceK := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,length]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]
    exact (Port6CK_ScalarRoundtrip.k _ (canonical ⟨i,by omega⟩)).symm

#print axioms k
end AspisR1.Port6CK_ArrayRoundtrip
end
