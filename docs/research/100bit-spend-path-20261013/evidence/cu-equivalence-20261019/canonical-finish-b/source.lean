import CuSavingsCanonicalDotsReduce
import CuSavingsCanonicalDotsField
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsFinish
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open CuSavingsRhoValue CuSavingsCanonicalDotsField
abbrev Raw := Array U64 4#usize

theorem new_finish (self : new_pairing.canonical.Dot) :
    new_pairing.canonical.Dot.finish self=.ok (reducedArray self.sums) := by
  have hr : new_pairing.canonical.reduce=AspisR1CuRho.field.M31.reduce_u64 :=
    funext CuSavingsCanonicalDotsReduce.reduce_eq_runtime
  unfold new_pairing.canonical.Dot.finish
  rw [hr]
  change (do let out ← AspisR1CuRho.core.array.Array.map
              (BuiltinFnMut U64 U32) self.sums AspisR1CuRho.field.M31.reduce_u64
             Result.ok out) = _
  rw [array_map_reduce]
  rfl

theorem old_finish (self : old_pairing.canonical.Dot) :
    old_pairing.canonical.Dot.finish self=.ok (reducedArray self.sums) := by
  have hr : old_pairing.canonical.reduce=AspisR1CuRho.field.M31.reduce_u64 := by
    funext x
    rw [CuSavingsCanonicalDotsReduce.old_reduce_eq,CuSavingsCanonicalDotsReduce.reduce_eq_runtime]
  unfold old_pairing.canonical.Dot.finish
  rw [hr]
  change (do let out ← AspisR1CuRho.core.array.Array.map
              (BuiltinFnMut U64 U32) self.sums AspisR1CuRho.field.M31.reduce_u64
             Result.ok out) = _
  rw [array_map_reduce]
  rfl

def qm (raw : Raw) : field.QM31 :=
  ⟨⟨canonicalWord (wordAt raw 0),canonicalWord (wordAt raw 1)⟩,
   ⟨canonicalWord (wordAt raw 2),canonicalWord (wordAt raw 3)⟩⟩

theorem qm_canonical (raw : Raw) : Canonical (qm raw) := by
  unfold Canonical qm
  exact ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩

def limbs (x : field.wide_exact.WideExact) : Array U32 8#usize :=
  Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
    x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem from_limbs (x : field.wide_exact.WideExact) (hc : WideCanonical x) :
    field.wide_exact.WideExact.from_limbs (limbs x)=.ok (some x) := by
  rcases hc with ⟨⟨ha,hb,hc,hd⟩,⟨he,hf,hg,hh⟩⟩
  simp [field.wide_exact.WideExact.from_limbs,limbs,Array.make,Array.index_usize,
    UScalar.le_equiv,field.P,not_le.mpr ha,not_le.mpr hb,not_le.mpr hc,
    not_le.mpr hd,not_le.mpr he,not_le.mpr hf,not_le.mpr hg,not_le.mpr hh]


def result (left right : Raw) : field.wide_exact.WideExact := ⟨qm left,qm right⟩

theorem result_canonical (left right : Raw) : WideCanonical (result left right) :=
  ⟨qm_canonical left,qm_canonical right⟩

theorem new_public_finish (self : new_pairing.EbyKDot) :
    new_pairing.EbyKDot.finish self=.ok (result self.c0.sums self.c1.sums) := by
  simp only [new_pairing.EbyKDot.finish,new_finish,new_pairing.canonical.Q.limbs,
    array_read _ 0#usize (by decide),array_read _ 1#usize (by decide),
    array_read _ 2#usize (by decide),array_read _ 3#usize (by decide),
    reduced_read,bind_tc_ok]
  change (do let out ← field.wide_exact.WideExact.from_limbs
              (limbs (result self.c0.sums self.c1.sums))
             core.option.Option.unwrap out) = _
  rw [from_limbs _ (result_canonical _ _)]
  rfl

theorem old_public_finish (self : old_pairing.EbyKDot) :
    old_pairing.EbyKDot.finish self=.ok (result self.c0.sums self.c1.sums) := by
  simp only [old_pairing.EbyKDot.finish,old_finish,old_pairing.qm31_of,
    old_pairing.canonical.Q.limbs,
    array_read _ 0#usize (by decide),array_read _ 1#usize (by decide),
    array_read _ 2#usize (by decide),array_read _ 3#usize (by decide),
    reduced_read,bind_tc_ok]
  exact new_identity (result self.c0.sums self.c1.sums) (result_canonical _ _)

#print axioms new_finish
#print axioms old_finish
#print axioms qm_canonical
#print axioms from_limbs
#print axioms result_canonical
#print axioms new_public_finish
#print axioms old_public_finish
end AspisR1.CuSavingsCanonicalDotsFinish
