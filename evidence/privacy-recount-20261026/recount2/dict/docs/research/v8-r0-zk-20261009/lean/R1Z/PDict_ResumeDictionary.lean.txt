import R1Z.PDict_Fence
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ResumeDictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_IOCarriers.native
abbrev selected := PDict_Fence.selected

theorem op163_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op163 = .ok 0#isize := rfl

theorem op164_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op164 = .ok 0#i64 := rfl

theorem op165_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op165 = .ok 0#i32 := rfl

theorem op166_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op166 = .ok 0#i16 := rfl

theorem op167_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op167 = .ok 0#i8 := rfl

theorem op168_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op168 = .ok 0#usize := rfl

theorem op169_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op169 = .ok 0#u64 := rfl

theorem op170_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op170 = .ok 0#u32 := rfl

theorem op171_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op171 = .ok 0#u16 := rfl

theorem op172_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op172 = .ok 0#u8 := rfl

theorem op173_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op173 = .ok 0#isize := rfl

theorem op174_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op174 = .ok 0#i64 := rfl

theorem op175_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op175 = .ok 0#i32 := rfl

theorem op176_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op176 = .ok 0#i16 := rfl

theorem op177_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op177 = .ok 0#i8 := rfl

theorem op178_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op178 = .ok 0#usize := rfl

theorem op179_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op179 = .ok 0#u64 := rfl

theorem op180_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op180 = .ok 0#u32 := rfl

theorem op181_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op181 = .ok 0#u16 := rfl

theorem op182_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op182 = .ok 0#u8 := rfl

theorem op183_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op183 = .ok () := rfl

theorem op184_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (x : typenum.uint.UTerm) :
    (selected base ops).op184 x = .ok x := rfl

theorem op188_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op188 = .ok true := rfl

theorem op189_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op189 = .ok 1#u8 := rfl

theorem op190_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op190 = .ok () := rfl

theorem op191_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op191 = .ok true := rfl

theorem op192_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op192 = .ok 1#u8 := rfl

theorem op193_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op193 = .ok () := rfl

theorem op194_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (x : typenum.bit.B1) :
    (selected base ops).op194 x = .ok x := rfl

theorem op196_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op196 = .ok Ordering.eq := rfl

theorem op197_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op197 = .ok Ordering.gt := rfl

theorem op198_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op198 = .ok false := rfl

theorem op199_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op199 = .ok 0#u8 := rfl

theorem op200_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op200 = .ok () := rfl

theorem op201_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op201 = .ok false := rfl

theorem op202_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op202 = .ok 0#u8 := rfl

theorem op203_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op203 = .ok () := rfl

theorem op204_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (x : typenum.bit.B0) :
    (selected base ops).op204 x = .ok x := rfl

theorem op141_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op141 u b = PDict_Numeric.op141 u b := rfl

theorem op142_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op142 u b = PDict_Numeric.op142 u b := rfl

theorem op143_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op143 u b = PDict_Numeric.op143 u b := rfl

theorem op144_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op144 u b = PDict_Numeric.op144 u b := rfl

theorem op145_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op145 u b = PDict_Numeric.op145 u b := rfl

theorem op146_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op146 u b = PDict_Numeric.op146 u b := rfl

theorem op147_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op147 u b = PDict_Numeric.op147 u b := rfl

theorem op148_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op148 u b = PDict_Numeric.op148 u b := rfl

theorem op149_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op149 u b = PDict_Numeric.op149 u b := rfl

theorem op150_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op150 u b = PDict_Numeric.op150 u b := rfl

theorem op151_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op151 u b = PDict_Numeric.op151 u b := rfl

theorem op152_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op152 u b = PDict_Numeric.op152 u b := rfl

theorem op153_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op153 u b = PDict_Numeric.op153 u b := rfl

theorem op154_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op154 u b = PDict_Numeric.op154 u b := rfl

theorem op155_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op155 u b = PDict_Numeric.op155 u b := rfl

theorem op156_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op156 u b = PDict_Numeric.op156 u b := rfl

theorem op157_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op157 u b = PDict_Numeric.op157 u b := rfl

theorem op158_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op158 u b = PDict_Numeric.op158 u b := rfl

theorem op159_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op159 u b = PDict_Numeric.op159 u b := rfl

theorem op160_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected base ops).op160 u b = PDict_Numeric.op160 u b := rfl

theorem op135_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {S : Type}
    (o : typenum.marker_traits.Ord S) (a b : typenum.uint.UTerm) (s : S) :
    (selected base ops).op135 o a b s = .ok s := rfl

theorem op136_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B S : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B)
    (o : typenum.marker_traits.Ord S) (a : typenum.uint.UTerm)
    (n : PDict_UIntOps.UInt U B) (s : S) :
    (selected base ops).op136 u b o a n s = .ok () := rfl

theorem op187_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {A B : Type}
    (a : A) (b : B) (c : typenum.Equal) :
    (selected base ops).op187 a b c = .ok () := rfl

theorem op195_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {A B : Type}
    (a : A) (b : B) (c : typenum.Less) :
    (selected base ops).op195 a b c = .ok () := rfl

theorem op0_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {T U : Type}
    (a : core.convert.AsRef T U) (x : T) :
    (selected base ops).op0 a x = a.as_ref x := rfl

theorem op1_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {T : Type} (s : Slice T) :
    (selected base ops).op1 s = .ok s := rfl

theorem op207_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op207 = .ok digest.core_api.TruncSide.Left := rfl

theorem op210_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (p b : Usize) :
    (selected base ops).op210 p b = .ok (decide (p < b)) := rfl

theorem op221_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op221 = .ok () := rfl

theorem op185_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {A B C O : Type}
    (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessOrEqualPrivate A B C O) (a : A) (b : B) :
    (selected base ops).op185 cmp next a b = PDict_Ordering.lessEq cmp next a b := rfl

theorem op186_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {A B C O : Type}
    (cmp : typenum.type_operators.Cmp A B C)
    (next : typenum.private.IsLessPrivate A B C O) (a : A) (b : B) :
    (selected base ops).op186 cmp next a b = PDict_Ordering.less cmp next a b := rfl

theorem op256_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (a b : r1_wire.Error) :
    (selected base ops).op256 a b = .ok (decide (a=b)) := PDict_WireError.exact a b

theorem op137_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {L R S O : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (s : typenum.marker_traits.Ord S)
    (next : typenum.private.PrivateCmp L R typenum.Greater O)
    (a : PDict_UIntOps.UInt L typenum.bit.B1) (b : PDict_UIntOps.UInt R typenum.bit.B0) (state : S) :
    (selected base ops).op137 l r s next a b state = next.private_cmp a.msb b.msb () := rfl

theorem op138_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {L R S O : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (s : typenum.marker_traits.Ord S) (next : typenum.private.PrivateCmp L R S O)
    (a : PDict_UIntOps.UInt L typenum.bit.B1) (b : PDict_UIntOps.UInt R typenum.bit.B1) (state : S) :
    (selected base ops).op138 l r s next a b state = next.private_cmp a.msb b.msb state := rfl

theorem op139_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {L R S O : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (s : typenum.marker_traits.Ord S) (next : typenum.private.PrivateCmp L R S O)
    (a : PDict_UIntOps.UInt L typenum.bit.B0) (b : PDict_UIntOps.UInt R typenum.bit.B0) (state : S) :
    (selected base ops).op139 l r s next a b state = next.private_cmp a.msb b.msb state := rfl

theorem op140_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {L R O IM : Type}
    (l : typenum.marker_traits.Unsigned L) (r : typenum.marker_traits.Unsigned R)
    (next : typenum.private.PrivateCmp L R typenum.Equal O)
    (marker : typenum.private.InternalMarker IM)
    (a : PDict_UIntOps.UInt L typenum.bit.B0) (b : PDict_UIntOps.UInt R typenum.bit.B0) :
    (selected base ops).op140 l r next marker a b = next.private_cmp a.msb b.msb () := rfl

theorem op161_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : core.default.Default U) (b : core.default.Default B) :
    (selected base ops).op161 u b = PDict_UIntOps.makeDefault u b := rfl

theorem op162_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {U B : Type}
    (u : core.clone.Clone U) (b : core.clone.Clone B) (x : PDict_UIntOps.UInt U B) :
    (selected base ops).op162 u b x = PDict_UIntOps.clone u b x := rfl

theorem op19_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op19 = .ok
      ⟨false,false,false,false,false,false,0#i32,438#u32⟩ := rfl

theorem op20_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (o : PDict_Options.Options) (b : Bool) :
    (selected base ops).op20 o b = .ok ({o with write := b},id) := rfl

theorem op21_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (o : PDict_Options.Options) (b : Bool) :
    (selected base ops).op21 o b = .ok ({o with create_new := b},id) := rfl

theorem op24_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (o : PDict_Options.Options) (m : U32) :
    (selected base ops).op24 o m = .ok ({o with mode := m},id) := rfl

theorem semantic_error (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (e : r1_wire.Error) :
    @prover.semantic_error (native base) (selected base ops) e =
      .ok (match e with
        | .ActivePole => verifier.Error.Rejected
        | _ => verifier.Error.Semantic) := by
  unfold prover.semantic_error
  change (do
    let b ← (selected base ops).op256 e .ActivePole
    if b then .ok verifier.Error.Rejected else .ok verifier.Error.Semantic) = _
  rw [op256_installed]
  cases e <;> rfl

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
#print axioms op137_installed
#print axioms op138_installed
#print axioms op139_installed
#print axioms op140_installed
#print axioms op161_installed
#print axioms op162_installed
#print axioms op19_installed
#print axioms op20_installed
#print axioms op21_installed
#print axioms op24_installed
#print axioms semantic_error


theorem op2_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (a b : core.io.error.ErrorKind) :
    (selected base ops).op2 a b = .ok (decide (a = b)) := PDict_ErrorKind.eq_exact a b

theorem op13_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op13 = PDict_Fence.fence := rfl

theorem op27_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (path : PDict_PathTypes.std.path.Path) :
    (selected base ops).op27 path = .ok path := rfl

theorem op206_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op206 = PDict_Publication.shaNew := rfl

theorem op211_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op211 (native base) (selected base ops) =
      fun {T : Type} value => .ok (PDict_Array32.flatten (T := T) value) := rfl

theorem op213_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op213 (native base) (selected base ops) =
      @PDict_DigestDelegates.digestUpdate (native base) := rfl

theorem op214_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op214 (native base) (selected base ops) =
      @PDict_DigestNew.digestNew (native base) := rfl

theorem op238_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (cell : Array U8 32#usize) :
    (selected base ops).op238 cell = .ok PDict_SaltClear.zero := rfl

#print axioms op2_installed
#print axioms op13_installed
#print axioms op27_installed
#print axioms op206_installed
#print axioms op211_installed
#print axioms op213_installed
#print axioms op214_installed
#print axioms op238_installed
end R1Z.PDict_ResumeDictionary
