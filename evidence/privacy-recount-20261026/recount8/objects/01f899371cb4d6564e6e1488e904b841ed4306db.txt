import R1Z.PDict_Ordering
import R1Z.PDict_MaskError
import R1Z.PDict_RetryCap
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Installed
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := PDict_Ordering.selected

theorem op163_installed (ops : ExternalFuns) :
    (selected ops).op163 = .ok 0#isize := rfl

theorem op164_installed (ops : ExternalFuns) :
    (selected ops).op164 = .ok 0#i64 := rfl

theorem op165_installed (ops : ExternalFuns) :
    (selected ops).op165 = .ok 0#i32 := rfl

theorem op166_installed (ops : ExternalFuns) :
    (selected ops).op166 = .ok 0#i16 := rfl

theorem op167_installed (ops : ExternalFuns) :
    (selected ops).op167 = .ok 0#i8 := rfl

theorem op168_installed (ops : ExternalFuns) :
    (selected ops).op168 = .ok 0#usize := rfl

theorem op169_installed (ops : ExternalFuns) :
    (selected ops).op169 = .ok 0#u64 := rfl

theorem op170_installed (ops : ExternalFuns) :
    (selected ops).op170 = .ok 0#u32 := rfl

theorem op171_installed (ops : ExternalFuns) :
    (selected ops).op171 = .ok 0#u16 := rfl

theorem op172_installed (ops : ExternalFuns) :
    (selected ops).op172 = .ok 0#u8 := rfl

theorem op173_installed (ops : ExternalFuns) :
    (selected ops).op173 = .ok 0#isize := rfl

theorem op174_installed (ops : ExternalFuns) :
    (selected ops).op174 = .ok 0#i64 := rfl

theorem op175_installed (ops : ExternalFuns) :
    (selected ops).op175 = .ok 0#i32 := rfl

theorem op176_installed (ops : ExternalFuns) :
    (selected ops).op176 = .ok 0#i16 := rfl

theorem op177_installed (ops : ExternalFuns) :
    (selected ops).op177 = .ok 0#i8 := rfl

theorem op178_installed (ops : ExternalFuns) :
    (selected ops).op178 = .ok 0#usize := rfl

theorem op179_installed (ops : ExternalFuns) :
    (selected ops).op179 = .ok 0#u64 := rfl

theorem op180_installed (ops : ExternalFuns) :
    (selected ops).op180 = .ok 0#u32 := rfl

theorem op181_installed (ops : ExternalFuns) :
    (selected ops).op181 = .ok 0#u16 := rfl

theorem op182_installed (ops : ExternalFuns) :
    (selected ops).op182 = .ok 0#u8 := rfl

theorem op183_installed (ops : ExternalFuns) :
    (selected ops).op183 = .ok () := rfl

theorem op184_installed (ops : ExternalFuns) (x : typenum.uint.UTerm) :
    (selected ops).op184 x = .ok x := rfl

theorem op188_installed (ops : ExternalFuns) :
    (selected ops).op188 = .ok true := rfl

theorem op189_installed (ops : ExternalFuns) :
    (selected ops).op189 = .ok 1#u8 := rfl

theorem op190_installed (ops : ExternalFuns) :
    (selected ops).op190 = .ok () := rfl

theorem op191_installed (ops : ExternalFuns) :
    (selected ops).op191 = .ok true := rfl

theorem op192_installed (ops : ExternalFuns) :
    (selected ops).op192 = .ok 1#u8 := rfl

theorem op193_installed (ops : ExternalFuns) :
    (selected ops).op193 = .ok () := rfl

theorem op194_installed (ops : ExternalFuns) (x : typenum.bit.B1) :
    (selected ops).op194 x = .ok x := rfl

theorem op196_installed (ops : ExternalFuns) :
    (selected ops).op196 = .ok Ordering.eq := rfl

theorem op197_installed (ops : ExternalFuns) :
    (selected ops).op197 = .ok Ordering.gt := rfl

theorem op198_installed (ops : ExternalFuns) :
    (selected ops).op198 = .ok false := rfl

theorem op199_installed (ops : ExternalFuns) :
    (selected ops).op199 = .ok 0#u8 := rfl

theorem op200_installed (ops : ExternalFuns) :
    (selected ops).op200 = .ok () := rfl

theorem op201_installed (ops : ExternalFuns) :
    (selected ops).op201 = .ok false := rfl

theorem op202_installed (ops : ExternalFuns) :
    (selected ops).op202 = .ok 0#u8 := rfl

theorem op203_installed (ops : ExternalFuns) :
    (selected ops).op203 = .ok () := rfl

theorem op204_installed (ops : ExternalFuns) (x : typenum.bit.B0) :
    (selected ops).op204 x = .ok x := rfl

theorem op141_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op141 u b = PDict_Numeric.op141 u b := rfl

theorem op142_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op142 u b = PDict_Numeric.op142 u b := rfl

theorem op143_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op143 u b = PDict_Numeric.op143 u b := rfl

theorem op144_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op144 u b = PDict_Numeric.op144 u b := rfl

theorem op145_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op145 u b = PDict_Numeric.op145 u b := rfl

theorem op146_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op146 u b = PDict_Numeric.op146 u b := rfl

theorem op147_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op147 u b = PDict_Numeric.op147 u b := rfl

theorem op148_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op148 u b = PDict_Numeric.op148 u b := rfl

theorem op149_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op149 u b = PDict_Numeric.op149 u b := rfl

theorem op150_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op150 u b = PDict_Numeric.op150 u b := rfl

theorem op151_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op151 u b = PDict_Numeric.op151 u b := rfl

theorem op152_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op152 u b = PDict_Numeric.op152 u b := rfl

theorem op153_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op153 u b = PDict_Numeric.op153 u b := rfl

theorem op154_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op154 u b = PDict_Numeric.op154 u b := rfl

theorem op155_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op155 u b = PDict_Numeric.op155 u b := rfl

theorem op156_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op156 u b = PDict_Numeric.op156 u b := rfl

theorem op157_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op157 u b = PDict_Numeric.op157 u b := rfl

theorem op158_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op158 u b = PDict_Numeric.op158 u b := rfl

theorem op159_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op159 u b = PDict_Numeric.op159 u b := rfl

theorem op160_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op160 u b = PDict_Numeric.op160 u b := rfl

theorem op135_installed (ops : ExternalFuns) {S : Type}
    (o : typenum.marker_traits.Ord S) (a b : typenum.uint.UTerm) (s : S) :
    (selected ops).op135 o a b s = .ok s := rfl

theorem op136_installed (ops : ExternalFuns) {U B S : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B)
    (o : typenum.marker_traits.Ord S) (a : typenum.uint.UTerm)
    (n : typenum.uint.UInt U B) (s : S) :
    (selected ops).op136 u b o a n s = .ok () := rfl

theorem op187_installed (ops : ExternalFuns) {A B : Type}
    (a : A) (b : B) (c : typenum.Equal) :
    (selected ops).op187 a b c = .ok () := rfl

theorem op195_installed (ops : ExternalFuns) {A B : Type}
    (a : A) (b : B) (c : typenum.Less) :
    (selected ops).op195 a b c = .ok () := rfl

theorem op0_installed (ops : ExternalFuns) {T U : Type}
    (a : core.convert.AsRef T U) (x : T) :
    (selected ops).op0 a x = a.as_ref x := rfl

theorem op1_installed (ops : ExternalFuns) {T : Type} (s : Slice T) :
    (selected ops).op1 s = .ok s := rfl

theorem op207_installed (ops : ExternalFuns) :
    (selected ops).op207 = .ok digest.core_api.TruncSide.Left := rfl

theorem op210_installed (ops : ExternalFuns) (p b : Usize) :
    (selected ops).op210 p b = .ok (decide (p < b)) := rfl

theorem op221_installed (ops : ExternalFuns) :
    (selected ops).op221 = .ok () := rfl

theorem op185_installed (ops : ExternalFuns) {A B C O : Type}
    (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessOrEqualPrivate A B C O) (a : A) (b : B) :
    (selected ops).op185 cmp next a b = PDict_Ordering.lessEq cmp next a b := rfl

theorem op186_installed (ops : ExternalFuns) {A B C O : Type}
    (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessPrivate A B C O) (a : A) (b : B) :
    (selected ops).op186 cmp next a b = PDict_Ordering.less cmp next a b := rfl

theorem op256_installed (ops : ExternalFuns) (a b : r1_wire.Error) :
    (selected ops).op256 a b = .ok (decide (a=b)) := PDict_WireError.exact a b

/-- The actual emitted semantic-error continuation consumes this final selector. -/
theorem semantic_error (ops : ExternalFuns) (e : r1_wire.Error) :
    @prover.semantic_error _ (selected ops) e =
      .ok (match e with
        | .ActivePole => verifier.Error.Rejected
        | _ => verifier.Error.Semantic) := by
  unfold prover.semantic_error
  change (do
    let b ← (selected ops).op256 e .ActivePole
    if b then .ok verifier.Error.Rejected else .ok verifier.Error.Semantic) = _
  rw [op256_installed]
  cases e <;> rfl

/-- Actual checker call, including its machine failure/divergence, is retained. -/
theorem public_check (ops : ExternalFuns) (v : transport.Variant)
    (ch : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
    (root : Array U8 32#usize) :
    @prover.public_check _ (selected ops) v ch root =
      (match v with
       | .S2 => do
         let (accepted,_) ← (selected ops).op232 ch
         if accepted then .ok (.Ok ()) else .ok (.Err verifier.Error.Rejected)
       | _ => .ok (.Err verifier.Error.Semantic)) := by
  cases v <;> rfl

#print axioms op163_installed
#print axioms op164_installed
#print axioms op165_installed
#print axioms op166_installed
#print axioms op167_installed
#print axioms op168_installed
#print axioms op169_installed
#print axioms op170_installed
#print axioms op171_installed
#print axioms op172_installed
#print axioms op173_installed
#print axioms op174_installed
#print axioms op175_installed
#print axioms op176_installed
#print axioms op177_installed
#print axioms op178_installed
#print axioms op179_installed
#print axioms op180_installed
#print axioms op181_installed
#print axioms op182_installed
#print axioms op183_installed
#print axioms op184_installed
#print axioms op188_installed
#print axioms op189_installed
#print axioms op190_installed
#print axioms op191_installed
#print axioms op192_installed
#print axioms op193_installed
#print axioms op194_installed
#print axioms op196_installed
#print axioms op197_installed
#print axioms op198_installed
#print axioms op199_installed
#print axioms op200_installed
#print axioms op201_installed
#print axioms op202_installed
#print axioms op203_installed
#print axioms op204_installed
#print axioms op141_installed
#print axioms op142_installed
#print axioms op143_installed
#print axioms op144_installed
#print axioms op145_installed
#print axioms op146_installed
#print axioms op147_installed
#print axioms op148_installed
#print axioms op149_installed
#print axioms op150_installed
#print axioms op151_installed
#print axioms op152_installed
#print axioms op153_installed
#print axioms op154_installed
#print axioms op155_installed
#print axioms op156_installed
#print axioms op157_installed
#print axioms op158_installed
#print axioms op159_installed
#print axioms op160_installed
#print axioms op135_installed
#print axioms op136_installed
#print axioms op187_installed
#print axioms op195_installed
#print axioms op0_installed
#print axioms op1_installed
#print axioms op207_installed
#print axioms op210_installed
#print axioms op221_installed
#print axioms op185_installed
#print axioms op186_installed
#print axioms op256_installed
#print axioms semantic_error
#print axioms public_check
end R1Z.PDict_Installed
