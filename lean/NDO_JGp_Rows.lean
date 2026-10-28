import NDO_JGp_Row0
import NDO_JGp_Row1
import NDO_JGp_Row2
import NDO_JGp_Row3
import NDO_JGp_Row4
import NDO_JGp_Row5
import NDO_JGp_Row6
import NDO_JGp_Row7
import NDO_JGp_Row8
import NDO_JGp_Row9
import JFv_TX2_DecodeNonzero
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Rows
open Aeneas Aeneas.Std Result
def input (i : Fin 10) (k : Fin 3) : Usize := match i.val,k.val with
  | 0,0 => 93499#usize
  | 0,1 => 93496#usize
  | 0,_ => 93499#usize
  | 1,0 => 147529#usize
  | 1,1 => 147528#usize
  | 1,_ => 147531#usize
  | 2,0 => 216823#usize
  | 2,1 => 216820#usize
  | 2,_ => 216823#usize
  | 3,0 => 245899#usize
  | 3,1 => 245896#usize
  | 3,_ => 245899#usize
  | 4,0 => 209371#usize
  | 4,1 => 209368#usize
  | 4,_ => 209371#usize
  | 5,0 => 192317#usize
  | 5,1 => 192316#usize
  | 5,_ => 192319#usize
  | 6,0 => 65593#usize
  | 6,1 => 65592#usize
  | 6,_ => 65595#usize
  | 7,0 => 183859#usize
  | 7,1 => 183856#usize
  | 7,_ => 183859#usize
  | 8,0 => 193093#usize
  | 8,1 => 193092#usize
  | 8,_ => 193095#usize
  | _,0 => 159813#usize
  | _,1 => 159812#usize
  | _,_ => 159815#usize
def value (i : Fin 10) : Port4C_GeometryGather.Row := match i.val with
  | 0 => JGp_Row0.value
  | 1 => JGp_Row1.value
  | 2 => JGp_Row2.value
  | 3 => JGp_Row3.value
  | 4 => JGp_Row4.value
  | 5 => JGp_Row5.value
  | 6 => JGp_Row6.value
  | 7 => JGp_Row7.value
  | 8 => JGp_Row8.value
  | _ => JGp_Row9.value
def query (i : Fin 10) : U32 := match i.val with
  | 0 => 93499#u32
  | 1 => 147529#u32
  | 2 => 216823#u32
  | 3 => 245899#u32
  | 4 => 209371#u32
  | 5 => 192317#u32
  | 6 => 65593#u32
  | 7 => 183859#u32
  | 8 => 193093#u32
  | _ => 159813#u32
def parent (i : Fin 10) : Usize := match i.val with
  | 0 => 23374#usize
  | 1 => 36882#usize
  | 2 => 54205#usize
  | 3 => 61474#usize
  | 4 => 52342#usize
  | 5 => 48079#usize
  | 6 => 16398#usize
  | 7 => 45964#usize
  | 8 => 48273#usize
  | _ => 39953#usize

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 10) :
    (JFv_TX2_GeometryOps.install err seed).op15 (input i 0)=ok (⟨(value i).x,(value i).y⟩ : SAQ_Geometry.Point) ∧
    (JFv_TX2_GeometryOps.install err seed).op14 (input i 1)=ok (value i).lineX ∧
    (JFv_TX2_GeometryOps.install err seed).op14 (input i 2)=ok (value i).lineY ∧
    JFv_TX2_NodeCall.sourceCall (value i).lineX=ok (value i).lineZ := by
  fin_cases i
  · exact JGp_Row0.source err seed
  · exact JGp_Row1.source err seed
  · exact JGp_Row2.source err seed
  · exact JGp_Row3.source err seed
  · exact JGp_Row4.source err seed
  · exact JGp_Row5.source err seed
  · exact JGp_Row6.source err seed
  · exact JGp_Row7.source err seed
  · exact JGp_Row8.source err seed
  · exact JGp_Row9.source err seed

theorem regular (i : Fin 10) : ∀ a∈(value i).words,a.val<2147483647 ∧ a≠0#u32 := by
  fin_cases i
  · exact JGp_Row0.regular
  · exact JGp_Row1.regular
  · exact JGp_Row2.regular
  · exact JGp_Row3.regular
  · exact JGp_Row4.regular
  · exact JGp_Row5.regular
  · exact JGp_Row6.regular
  · exact JGp_Row7.regular
  · exact JGp_Row8.regular
  · exact JGp_Row9.regular

theorem nonzero (i : Fin 10) : ∀ a∈(value i).words,S7JoinBasisMachine.decode a≠0 := by
  intro a ha
  obtain ⟨hc,hn⟩ := regular i a ha
  exact JFv_TX2_DecodeNonzero.source a hc hn

theorem addresses (i : Fin 10) :
    lift (UScalar.cast .Usize (query i))=ok (input i 0) ∧
    input i 0/4#usize=ok (parent i) ∧
    Usize.wrapping_mul (parent i) 4#usize=input i 1 ∧
    Usize.wrapping_add (input i 1) 3#usize=input i 2 := by
  have cap : 262144 < UScalar.size .Usize := by
    cases System.Platform.numBits_eq <;> norm_num [UScalar.size,Usize.size,Usize.numBits,UScalarTy.Usize_numBits_eq, *]
  fin_cases i
  · change lift (UScalar.cast .Usize 93499#u32)=ok 93499#usize ∧
      93499#usize/4#usize=ok 23374#usize ∧
      Usize.wrapping_mul 23374#usize 4#usize=93496#usize ∧
      Usize.wrapping_add 93496#usize 3#usize=93499#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 93499#u32=93499#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 93496<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 93499<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 147529#u32)=ok 147529#usize ∧
      147529#usize/4#usize=ok 36882#usize ∧
      Usize.wrapping_mul 36882#usize 4#usize=147528#usize ∧
      Usize.wrapping_add 147528#usize 3#usize=147531#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 147529#u32=147529#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 147528<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 147531<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 216823#u32)=ok 216823#usize ∧
      216823#usize/4#usize=ok 54205#usize ∧
      Usize.wrapping_mul 54205#usize 4#usize=216820#usize ∧
      Usize.wrapping_add 216820#usize 3#usize=216823#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 216823#u32=216823#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 216820<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 216823<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 245899#u32)=ok 245899#usize ∧
      245899#usize/4#usize=ok 61474#usize ∧
      Usize.wrapping_mul 61474#usize 4#usize=245896#usize ∧
      Usize.wrapping_add 245896#usize 3#usize=245899#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 245899#u32=245899#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 245896<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 245899<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 209371#u32)=ok 209371#usize ∧
      209371#usize/4#usize=ok 52342#usize ∧
      Usize.wrapping_mul 52342#usize 4#usize=209368#usize ∧
      Usize.wrapping_add 209368#usize 3#usize=209371#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 209371#u32=209371#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 209368<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 209371<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 192317#u32)=ok 192317#usize ∧
      192317#usize/4#usize=ok 48079#usize ∧
      Usize.wrapping_mul 48079#usize 4#usize=192316#usize ∧
      Usize.wrapping_add 192316#usize 3#usize=192319#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 192317#u32=192317#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 192316<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 192319<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 65593#u32)=ok 65593#usize ∧
      65593#usize/4#usize=ok 16398#usize ∧
      Usize.wrapping_mul 16398#usize 4#usize=65592#usize ∧
      Usize.wrapping_add 65592#usize 3#usize=65595#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 65593#u32=65593#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 65592<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 65595<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 183859#u32)=ok 183859#usize ∧
      183859#usize/4#usize=ok 45964#usize ∧
      Usize.wrapping_mul 45964#usize 4#usize=183856#usize ∧
      Usize.wrapping_add 183856#usize 3#usize=183859#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 183859#u32=183859#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 183856<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 183859<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 193093#u32)=ok 193093#usize ∧
      193093#usize/4#usize=ok 48273#usize ∧
      Usize.wrapping_mul 48273#usize 4#usize=193092#usize ∧
      Usize.wrapping_add 193092#usize 3#usize=193095#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 193093#u32=193093#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 193092<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 193095<UScalar.size .Usize;omega)
  · change lift (UScalar.cast .Usize 159813#u32)=ok 159813#usize ∧
      159813#usize/4#usize=ok 39953#usize ∧
      Usize.wrapping_mul 39953#usize 4#usize=159812#usize ∧
      Usize.wrapping_add 159812#usize 3#usize=159815#usize
    refine ⟨?_,rfl,?_,?_⟩
    · have hc : UScalar.cast .Usize 159813#u32=159813#usize := by scalar_tac
      rw [hc];rfl
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_mul_val_eq]
      exact Nat.mod_eq_of_lt (by change 159812<UScalar.size .Usize;omega)
    · apply UScalar.eq_of_val_eq
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt (by change 159815<UScalar.size .Usize;omega)
theorem fibres {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C)
    (i : Fin 10) (k : Fin 3) :
    (JFv_TX2_GeometryOps.install err seed).op12 (input i k)=ok (.Ok (input i k)) := by
  change SAQ_Constructor.fibre err (input i k)=_
  have bound : input i k<262144#usize := by fin_cases i <;> fin_cases k <;> decide
  simp only [SAQ_Constructor.fibre,if_pos bound]
#print axioms source
#print axioms regular
#print axioms nonzero
#print axioms addresses
#print axioms fibres
end AspisR1.JGp_Rows
end
