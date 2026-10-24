import S1QueryMaterializeEffectsV1
import S1QueryReadPairProgramV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open PreparedHashCode

def materializeReads {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
    (hash : H) (state0 : Bytes32) : Code (Blocks8 × Blocks8) := do
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let a1 ← QueryPair.readState aspis_coreDigest32Inst hash state0 1#u8
  let (_, index_mut_back) ← Array.index_mut_usize blocks 0#usize
  let a2 ← QueryPair.readState aspis_coreDigest32Inst hash state0 2#u8
  let blocks1 := index_mut_back a2
  let state ← Array.index_usize blocks1 0#usize
  let a3 ← QueryPair.readState aspis_coreDigest32Inst hash state 1#u8
  let blocks2 := index_mut_back a1
  let blocks3 ← Array.update blocks2 1#usize a3
  let a4 ← QueryPair.readState aspis_coreDigest32Inst hash state 2#u8
  let blocks4 ← Array.update blocks1 1#usize a4
  let state1 ← Array.index_usize blocks4 1#usize
  let a5 ← QueryPair.readState aspis_coreDigest32Inst hash state1 1#u8
  let blocks5 ← Array.update blocks3 2#usize a5
  let a6 ← QueryPair.readState aspis_coreDigest32Inst hash state1 2#u8
  let blocks6 ← Array.update blocks4 2#usize a6
  let state2 ← Array.index_usize blocks6 2#usize
  let a7 ← QueryPair.readState aspis_coreDigest32Inst hash state2 1#u8
  let blocks7 ← Array.update blocks5 3#usize a7
  let a8 ← QueryPair.readState aspis_coreDigest32Inst hash state2 2#u8
  let blocks8 ← Array.update blocks6 3#usize a8
  let state3 ← Array.index_usize blocks8 3#usize
  let a9 ← QueryPair.readState aspis_coreDigest32Inst hash state3 1#u8
  let blocks9 ← Array.update blocks7 4#usize a9
  let a10 ← QueryPair.readState aspis_coreDigest32Inst hash state3 2#u8
  let blocks10 ← Array.update blocks8 4#usize a10
  let state4 ← Array.index_usize blocks10 4#usize
  let a11 ← QueryPair.readState aspis_coreDigest32Inst hash state4 1#u8
  let blocks11 ← Array.update blocks9 5#usize a11
  let a12 ← QueryPair.readState aspis_coreDigest32Inst hash state4 2#u8
  let blocks12 ← Array.update blocks10 5#usize a12
  let state5 ← Array.index_usize blocks12 5#usize
  let a13 ← QueryPair.readState aspis_coreDigest32Inst hash state5 1#u8
  let blocks13 ← Array.update blocks11 6#usize a13
  let a14 ← QueryPair.readState aspis_coreDigest32Inst hash state5 2#u8
  let blocks14 ← Array.update blocks12 6#usize a14
  let state6 ← Array.index_usize blocks14 6#usize
  let a15 ← QueryPair.readState aspis_coreDigest32Inst hash state6 1#u8
  let blocks15 ← Array.update blocks13 7#usize a15
  let a16 ← QueryPair.readState aspis_coreDigest32Inst hash state6 2#u8
  let blocks16 ← Array.update blocks14 7#usize a16
  let _ ← Array.index_usize blocks16 7#usize

  pure (blocks15,blocks16)

def materializePairs {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (state0 : Bytes32) : Code (Blocks8 × Blocks8) := do
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let a1 ← QueryPair.readState D hash state0 1#u8
  let (_,back) ← Array.index_mut_usize blocks 0#usize
  let a2 ← QueryPair.readState D hash state0 2#u8
  let advances := back a2
  let state ← Array.index_usize advances 0#usize
  let (state1,blocks3,blocks4) ← QueryPair.pairStep D hash state (back a1) advances 1#usize
  let (state2,blocks5,blocks6) ← QueryPair.pairStep D hash state1 blocks3 blocks4 2#usize
  let (state3,blocks7,blocks8) ← QueryPair.pairStep D hash state2 blocks5 blocks6 3#usize
  let (state4,blocks9,blocks10) ← QueryPair.pairStep D hash state3 blocks7 blocks8 4#usize
  let (state5,blocks11,blocks12) ← QueryPair.pairStep D hash state4 blocks9 blocks10 5#usize
  let (state6,blocks13,blocks14) ← QueryPair.pairStep D hash state5 blocks11 blocks12 6#usize
  let (_,blocks15,blocks16) ← QueryPair.pairStep D hash state6 blocks13 blocks14 7#usize
  pure (blocks15,blocks16)

private theorem code_bind_congr {A B : Type} (p : Code A) (f g : A → Code B)
    (h : ∀ a, f a=g a) : (p >>= f)=(p >>= g) :=
  congrArg (fun next => p >>= next) (funext h)

theorem materialize_code_eq_reads {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (state : Bytes32) :
    materialize effects D hash state=materializeReads D hash state := by
  unfold materialize materializeReads QueryPair.readState
  repeat' first
    | (with_reducible apply code_bind_congr; intro x)
    | (conv => rhs; rw [code_bind_assoc])
    | (with_reducible rfl)
    | split

theorem materialize_code_eq_pairs {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (state : Bytes32) :
    materialize effects D hash state=materializePairs D hash state := by
  rw [materialize_code_eq_reads]
  unfold materializeReads materializePairs QueryPair.pairStep
  repeat' first
    | (with_reducible apply code_bind_congr; intro x)
    | (conv => rhs; rw [code_bind_assoc])
    | (with_reducible rfl)
    | split

#print axioms materialize_code_eq_reads
#print axioms materialize_code_eq_pairs
end AspisR1PublicPreparation.PreparedQueryMaterialize
