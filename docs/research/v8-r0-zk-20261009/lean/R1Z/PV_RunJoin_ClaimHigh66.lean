import R1Z.PV_RunJoin_ClaimImage48
import R1Z.PV_RunJoin_HighDomain40
import R1Z.PV_RunJoin_ZeroWord40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimHigh66
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47

/-- The embedded subfield has a literal zero upper half. Only the fixed
sixteen-byte suffix is reduced here. -/
theorem cell (q : Old.Q) :
    ((PV_RunJoin_FlatBytes35.wire (ProverRwDictionaryTower.fromW
      (ProverCommitNativeOps47.embedded q))).val).drop 16=List.replicate 16 (0#u8) := by
  simp only [ProverCommitNativeOps47.embedded,ProverRwDictionaryTower.fromW,
    ProverRwDictionaryTower.fromQ,ProverRwDictionaryTower.fromC,
    ProverCommitRelease47.convE,ProverCommitRelease47.convQ,ProverCommitRelease47.convC,
    ProverCommitSubfieldOps47.embedded,ProverCommitSubfieldOps47.zero,
    ProverCommitPrimitive47.fromQ,ProverCommitPrimitive47.fromC,
    PV_RunJoin_FlatBytes35.wire,Array.make,
    List.drop_succ_cons,List.drop_zero]
  simp only [PV_RunJoin_FlatBytes35.byte,PV_RunJoin_ZeroWord40.bytes,
    List.getElem_cons_zero,List.getElem_cons_succ]
  rfl

theorem byte (q : Old.Q) (j : Nat) (lo : 16≤j) (hi : j<32) :
    (PV_RunJoin_FlatBytes35.wire (ProverRwDictionaryTower.fromW
      (ProverCommitNativeOps47.embedded q))).val[j]?=some 0#u8 := by
  have h := congrArg (fun xs : List U8 => xs[j-16]?) (cell q)
  simpa only [List.getElem?_drop,Nat.add_sub_of_le lo,List.getElem?_replicate,
    show j-16<16 from (by omega),if_pos] using h

theorem high (qs : List Old.Q) :
    PV_RunJoin_HighDomain40.HighZero (PV_RunJoin_ClaimImage48.bytes
      (qs.map (fun q => ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded q)))) := by
  intro k j bound lo hi
  induction qs generalizing k with
  | nil => simp only [List.map_nil,PV_RunJoin_ClaimImage48.bytes,List.length_nil] at bound;omega
  | cons q qs ih =>
    simp only [List.map_cons,PV_RunJoin_ClaimImage48.bytes] at bound ⊢
    have len : (PV_RunJoin_FlatBytes35.wire (ProverRwDictionaryTower.fromW
        (ProverCommitNativeOps47.embedded q))).val.length=32 :=
      (PV_RunJoin_FlatBytes35.wire _).property
    cases k with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_add]
      rw [List.getElem?_append_left (by rw [len];exact hi)]
      exact byte q j lo hi
    | succ k =>
      rw [List.getElem?_append_right (by rw [len];omega),len]
      have ix : 32*(k+1)+j-32=32*k+j := by omega
      rw [ix]
      apply ih k
      rw [List.length_append,len] at bound
      omega

#print axioms cell
#print axioms byte
#print axioms high
end R1Z.PV_RunJoin_ClaimHigh66
