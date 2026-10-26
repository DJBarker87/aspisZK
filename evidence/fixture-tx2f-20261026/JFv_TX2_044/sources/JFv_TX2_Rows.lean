import JFv_TX2_Row10
import JFv_TX2_Row11
import JFv_TX2_Row12
import JFv_TX2_Row13
import JFv_TX2_Row14
import JFv_TX2_Row15
import JFv_TX2_Row16
import JFv_TX2_Row17
import JFv_TX2_Row18
import JFv_TX2_Row19
import JFv_TX2_Row20
import JFv_TX2_Row21
import JFs_TX2_GeometryPoints
import JFv_TX2_DecodeNonzero
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Rows
open Aeneas Aeneas.Std Result
abbrev input := JFs_TX2_GeometryPoints.input
def value (i : Fin 12) : Port4C_GeometryGather.Row := match i.val with
  | 0 => JFv_TX2_Row10.value
  | 1 => JFv_TX2_Row11.value
  | 2 => JFv_TX2_Row12.value
  | 3 => JFv_TX2_Row13.value
  | 4 => JFv_TX2_Row14.value
  | 5 => JFv_TX2_Row15.value
  | 6 => JFv_TX2_Row16.value
  | 7 => JFv_TX2_Row17.value
  | 8 => JFv_TX2_Row18.value
  | 9 => JFv_TX2_Row19.value
  | 10 => JFv_TX2_Row20.value
  | _ => JFv_TX2_Row21.value
def query (i : Fin 12) : U32 := match i.val with
  | 0 => 132355#u32
  | 1 => 218094#u32
  | 2 => 178080#u32
  | 3 => 149624#u32
  | 4 => 166165#u32
  | 5 => 42158#u32
  | 6 => 179622#u32
  | 7 => 21248#u32
  | 8 => 63860#u32
  | 9 => 55377#u32
  | 10 => 185637#u32
  | _ => 14297#u32
def parent (i : Fin 12) : Usize := match i.val with
  | 0 => 33088#usize
  | 1 => 54523#usize
  | 2 => 44520#usize
  | 3 => 37406#usize
  | 4 => 41541#usize
  | 5 => 10539#usize
  | 6 => 44905#usize
  | 7 => 5312#usize
  | 8 => 15965#usize
  | 9 => 13844#usize
  | 10 => 46409#usize
  | _ => 3574#usize

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) :
    (JFv_TX2_GeometryOps.install err seed).op15 (input i 0)=ok (⟨(value i).x,(value i).y⟩ : SAQ_Geometry.Point) ∧
    (JFv_TX2_GeometryOps.install err seed).op14 (input i 1)=ok (value i).lineX ∧
    (JFv_TX2_GeometryOps.install err seed).op14 (input i 2)=ok (value i).lineY ∧
    JFv_TX2_NodeCall.sourceCall (value i).lineX=ok (value i).lineZ := by
  fin_cases i
  · exact JFv_TX2_Row10.source err seed
  · exact JFv_TX2_Row11.source err seed
  · exact JFv_TX2_Row12.source err seed
  · exact JFv_TX2_Row13.source err seed
  · exact JFv_TX2_Row14.source err seed
  · exact JFv_TX2_Row15.source err seed
  · exact JFv_TX2_Row16.source err seed
  · exact JFv_TX2_Row17.source err seed
  · exact JFv_TX2_Row18.source err seed
  · exact JFv_TX2_Row19.source err seed
  · exact JFv_TX2_Row20.source err seed
  · exact JFv_TX2_Row21.source err seed

theorem regular (i : Fin 12) : ∀ a∈(value i).words,a.val<2147483647 ∧ a≠0#u32 := by
  fin_cases i
  · exact JFv_TX2_Row10.regular
  · exact JFv_TX2_Row11.regular
  · exact JFv_TX2_Row12.regular
  · exact JFv_TX2_Row13.regular
  · exact JFv_TX2_Row14.regular
  · exact JFv_TX2_Row15.regular
  · exact JFv_TX2_Row16.regular
  · exact JFv_TX2_Row17.regular
  · exact JFv_TX2_Row18.regular
  · exact JFv_TX2_Row19.regular
  · exact JFv_TX2_Row20.regular
  · exact JFv_TX2_Row21.regular

theorem nonzero (i : Fin 12) : ∀ a∈(value i).words,S7JoinBasisMachine.decode a≠0 := by
  intro a ha
  obtain ⟨hc,hn⟩ := regular i a ha
  exact JFv_TX2_DecodeNonzero.source a hc hn

theorem addresses (i : Fin 12) :
    lift (UScalar.cast .Usize (query i))=ok (input i 0) ∧
    input i 0/4#usize=ok (parent i) ∧
    Usize.wrapping_mul (parent i) 4#usize=input i 1 ∧
    Usize.wrapping_add (input i 1) 3#usize=input i 2 := by
  fin_cases i <;> refine ⟨rfl,rfl,rfl,?_⟩
  all_goals
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)

theorem fibres {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C)
    (i : Fin 12) (k : Fin 3) :
    (JFv_TX2_GeometryOps.install err seed).op12 (input i k)=ok (.Ok (input i k)) := by
  change SAQ_Constructor.fibre err (input i k)=_
  have bound : input i k<262144#usize := by fin_cases i <;> fin_cases k <;> decide
  simp only [SAQ_Constructor.fibre,if_pos bound]

#print axioms source
#print axioms regular
#print axioms nonzero
#print axioms addresses
#print axioms fibres
end AspisR1.JFv_TX2_Rows
end
