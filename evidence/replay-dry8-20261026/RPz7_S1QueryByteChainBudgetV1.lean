import RPz7_S1QueryMaterializeModelV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedHashCode.QueryPair
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

theorem pairedBytesProgram_reads {A : Type} (out : List State → List State → A)
    (n : Nat) (state : State) (blocks advances : List State) (oracle : Bytes → State) :
    (eval oracle (pairedBytesProgram out n state blocks advances)).1.length=2*n := by
  induction n generalizing state blocks advances with
  | zero => rfl
  | succ n ih =>
    simp only [pairedBytesProgram,eval,List.length_cons,ih]
    omega

end AspisR1PublicPreparation.PreparedHashCode.QueryPair
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open PreparedHashCode.QueryPair

theorem modelMaterialize_reads {M Cv : Type} {L : Nat} (p : Params M Cv L)
    (state : Bytes32) (oracle : Bytes → State) :
    (eval oracle (modelMaterialize p state)).1.length=16 := by
  unfold modelMaterialize
  rw [← pairedBytesProgram_eq_model p packEight 8 (decodeState state) [] []]
  exact pairedBytesProgram_reads packEight 8 (decodeState state) [] [] oracle

#print axioms PreparedHashCode.QueryPair.pairedBytesProgram_reads
#print axioms modelMaterialize_reads
end AspisR1PublicPreparation.PreparedQueryMaterialize
