import R1Z.PV_RunJoin_FourReader73
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WireReaders73
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FlatBytes35 (wire)
attribute [local irreducible] PV_RunJoin_FlatBytes35.byte

theorem word0 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 0#usize 1#usize 2#usize 3#usize=ok x.c0.c0.a := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word0

theorem word1 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 4#usize 5#usize 6#usize 7#usize=ok x.c0.c0.b := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word1

theorem word2 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 8#usize 9#usize 10#usize 11#usize=ok x.c0.c1.a := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word2

theorem word3 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 12#usize 13#usize 14#usize 15#usize=ok x.c0.c1.b := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word3

theorem word4 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 16#usize 17#usize 18#usize 19#usize=ok x.c1.c0.a := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word4

theorem word5 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 20#usize 21#usize 22#usize 23#usize=ok x.c1.c0.b := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word5

theorem word6 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 24#usize 25#usize 26#usize 27#usize=ok x.c1.c1.a := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word6

theorem word7 (x : aspis_core.field.wide_exact.WideExact) :
    PV_RunJoin_FourReader73.read (Array.to_slice (wire x)) 28#usize 29#usize 30#usize 31#usize=ok x.c1.c1.b := by
  apply PV_RunJoin_FourReader73.complete
  all_goals
    rw [PV_RunJoin_MergeArray35.slice_read,
      ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
    rfl

#print axioms word7
end R1Z.PV_RunJoin_WireReaders73
