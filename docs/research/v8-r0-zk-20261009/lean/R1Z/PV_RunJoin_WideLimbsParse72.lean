import R1Z.PV_RunJoin_FieldData34
import R1Z.ProverRwDictionaryBytesSource
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WideLimbsParse72
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev P := ProverRwDictionaryBytesSource.aspis_core.field.P

def Canonical (x : W) : Prop :=
  x.c0.c0.a.val<P.val ∧ x.c0.c0.b.val<P.val ∧
  x.c0.c1.a.val<P.val ∧ x.c0.c1.b.val<P.val ∧
  x.c1.c0.a.val<P.val ∧ x.c1.c0.b.val<P.val ∧
  x.c1.c1.a.val<P.val ∧ x.c1.c1.b.val<P.val

def limbs (x : W) : Array U32 8#usize := Array.make 8#usize
  [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem complete (x : W) (canonical : Canonical x) :
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs (limbs x)=ok (some x) := by
  rcases canonical with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have b0 : ¬x.c0.c0.a≥P := Nat.not_le.mpr h0
  have b1 : ¬x.c0.c0.b≥P := Nat.not_le.mpr h1
  have b2 : ¬x.c0.c1.a≥P := Nat.not_le.mpr h2
  have b3 : ¬x.c0.c1.b≥P := Nat.not_le.mpr h3
  have b4 : ¬x.c1.c0.a≥P := Nat.not_le.mpr h4
  have b5 : ¬x.c1.c0.b≥P := Nat.not_le.mpr h5
  have b6 : ¬x.c1.c1.a≥P := Nat.not_le.mpr h6
  have b7 : ¬x.c1.c1.b≥P := Nat.not_le.mpr h7
  unfold ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs
  repeat' (rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]; simp only [bind_tc_ok,b0,b1,b2,b3,b4,b5,b6,b7,if_false])
  simp only [limbs,Array.make,UScalar.ofNatCore_val_eq,List.getElem_cons_zero,
    List.getElem_cons_succ,b0,b1,b2,b3,b4,b5,b6,b7,if_false]
  all_goals rfl

#print axioms Canonical
#print axioms limbs
#print axioms complete
end R1Z.PV_RunJoin_WideLimbsParse72
