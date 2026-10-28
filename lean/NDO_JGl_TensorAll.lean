import NDO_JGl_TensorNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_TensorAll
open Aeneas Aeneas.Std
open FIv_NativeValue (decode)
open FIw_ArrayValue (decoded)
theorem high (i : Fin 64) : FJa_TensorMeaning.weight
    ((JFu_TerminalPrefix.alpha.val.take 6).map decode) i.val=decoded JGl_NumericData.high i := by
  have hi := i.isLt
  by_cases h0 : i.val<8
  · let j : Fin 8 := ⟨i.val-0,by omega⟩
    have eq : 0+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorHigh0.value j
  by_cases h1 : i.val<16
  · let j : Fin 8 := ⟨i.val-8,by omega⟩
    have eq : 8+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorHigh1.value j
  by_cases h2 : i.val<24
  · let j : Fin 8 := ⟨i.val-16,by omega⟩
    have eq : 16+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorHigh2.value j
  by_cases h3 : i.val<32
  · let j : Fin 8 := ⟨i.val-24,by omega⟩
    have eq : 24+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorHigh3.value j
  by_cases h4 : i.val<40
  · let j : Fin 8 := ⟨i.val-32,by omega⟩
    have eq : 32+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorHigh4.value j
  by_cases h5 : i.val<48
  · let j : Fin 8 := ⟨i.val-40,by omega⟩
    have eq : 40+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorHigh5.value j
  by_cases h6 : i.val<56
  · let j : Fin 8 := ⟨i.val-48,by omega⟩
    have eq : 48+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorHigh6.value j
  let j : Fin 8 := ⟨i.val-56,by omega⟩
  have eq : 56+j.val=i.val := by dsimp only [j];omega
  simpa only [eq,Fin.eta] using JGl_TensorHigh7.value j
#print axioms high
theorem low (i : Fin 16) : FJa_TensorMeaning.weight
    ((JFu_TerminalPrefix.alpha.val.drop 6).map decode) i.val=decoded JGl_NumericData.low i := by
  have hi := i.isLt
  by_cases h0 : i.val<8
  · let j : Fin 8 := ⟨i.val-0,by omega⟩
    have eq : 0+j.val=i.val := by dsimp only [j];omega
    simpa only [eq,Fin.eta] using JGl_TensorLow0.value j
  let j : Fin 8 := ⟨i.val-8,by omega⟩
  have eq : 8+j.val=i.val := by dsimp only [j];omega
  simpa only [eq,Fin.eta] using JGl_TensorLow1.value j
#print axioms low
end AspisR1.JGl_TensorAll
end
