import NDO_JFv_TX2_Row10
import NDO_JFv_TX2_Row11
import NDO_JFv_TX2_Row12
import NDO_JFv_TX2_Row13
import NDO_JFv_TX2_Row14
import NDO_JFv_TX2_Row15
import NDO_JFv_TX2_Row16
import NDO_JFv_TX2_Row17
import NDO_JFv_TX2_Row18
import NDO_JFv_TX2_Row19
import NDO_JFv_TX2_Row20
import NDO_JFv_TX2_Row21
import NDO_JFs_TX2_GeometryPoints
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
  have cap : 262144 < UScalar.size .Usize := by
    cases System.Platform.numBits_eq <;> norm_num [UScalar.size,Usize.size,Usize.numBits,UScalarTy.Usize_numBits_eq, *]
  fin_cases i
  · change lift (UScalar.cast .Usize 132355#u32)=ok 132355#usize ∧
      132355#usize/4#usize=ok 33088#usize ∧
      Usize.wrapping_mul 33088#usize 4#usize=132352#usize ∧
      Usize.wrapping_add 132352#usize 3#usize=132355#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 132355#u32=132355#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 132352<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 132355<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 218094#u32)=ok 218094#usize ∧
      218094#usize/4#usize=ok 54523#usize ∧
      Usize.wrapping_mul 54523#usize 4#usize=218092#usize ∧
      Usize.wrapping_add 218092#usize 3#usize=218095#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 218094#u32=218094#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 218092<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 218095<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 178080#u32)=ok 178080#usize ∧
      178080#usize/4#usize=ok 44520#usize ∧
      Usize.wrapping_mul 44520#usize 4#usize=178080#usize ∧
      Usize.wrapping_add 178080#usize 3#usize=178083#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 178080#u32=178080#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 178080<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 178083<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 149624#u32)=ok 149624#usize ∧
      149624#usize/4#usize=ok 37406#usize ∧
      Usize.wrapping_mul 37406#usize 4#usize=149624#usize ∧
      Usize.wrapping_add 149624#usize 3#usize=149627#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 149624#u32=149624#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 149624<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 149627<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 166165#u32)=ok 166165#usize ∧
      166165#usize/4#usize=ok 41541#usize ∧
      Usize.wrapping_mul 41541#usize 4#usize=166164#usize ∧
      Usize.wrapping_add 166164#usize 3#usize=166167#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 166165#u32=166165#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 166164<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 166167<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 42158#u32)=ok 42158#usize ∧
      42158#usize/4#usize=ok 10539#usize ∧
      Usize.wrapping_mul 10539#usize 4#usize=42156#usize ∧
      Usize.wrapping_add 42156#usize 3#usize=42159#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 42158#u32=42158#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 42156<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 42159<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 179622#u32)=ok 179622#usize ∧
      179622#usize/4#usize=ok 44905#usize ∧
      Usize.wrapping_mul 44905#usize 4#usize=179620#usize ∧
      Usize.wrapping_add 179620#usize 3#usize=179623#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 179622#u32=179622#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 179620<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 179623<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 21248#u32)=ok 21248#usize ∧
      21248#usize/4#usize=ok 5312#usize ∧
      Usize.wrapping_mul 5312#usize 4#usize=21248#usize ∧
      Usize.wrapping_add 21248#usize 3#usize=21251#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 21248#u32=21248#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 21248<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 21251<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 63860#u32)=ok 63860#usize ∧
      63860#usize/4#usize=ok 15965#usize ∧
      Usize.wrapping_mul 15965#usize 4#usize=63860#usize ∧
      Usize.wrapping_add 63860#usize 3#usize=63863#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 63860#u32=63860#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 63860<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 63863<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 55377#u32)=ok 55377#usize ∧
      55377#usize/4#usize=ok 13844#usize ∧
      Usize.wrapping_mul 13844#usize 4#usize=55376#usize ∧
      Usize.wrapping_add 55376#usize 3#usize=55379#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 55377#u32=55377#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 55376<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 55379<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 185637#u32)=ok 185637#usize ∧
      185637#usize/4#usize=ok 46409#usize ∧
      Usize.wrapping_mul 46409#usize 4#usize=185636#usize ∧
      Usize.wrapping_add 185636#usize 3#usize=185639#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 185637#u32=185637#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 185636<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 185639<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 14297#u32)=ok 14297#usize ∧
      14297#usize/4#usize=ok 3574#usize ∧
      Usize.wrapping_mul 3574#usize 4#usize=14296#usize ∧
      Usize.wrapping_add 14296#usize 3#usize=14299#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 14297#u32=14297#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 14296<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 14299<UScalar.size .Usize;omega)

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
