import XRp_IndexedWitness
import XRp_LoopReplay
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRp_IndexedTrace
open XRp_DivisionWitness XRp_IndexedWitness XRp_LoopReplay
abbrev State := Array U32 8#usize × U64 × Usize
def step (s : State) := AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body s.1 s.2.1 s.2.2

theorem zero2 : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 2#usize =
    ok (.cont (rank,0#u64,1#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hp : 2#usize > 0#usize := by scalar_tac
  have hs : 2#usize - 1#usize = ok 1#usize := by
    obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=2#usize) (y:=1#usize) (by scalar_tac))
    have he : z = 1#usize := UScalar.eq_of_val_eq (by simpa using hv)
    exact hz.trans (congrArg ok he)
  simp only [if_pos hp,hs,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl
#print axioms zero2

theorem zero3 : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 3#usize =
    ok (.cont (rank,0#u64,2#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hp : 3#usize > 0#usize := by scalar_tac
  have hs : 3#usize - 1#usize = ok 2#usize := by
    obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=3#usize) (y:=1#usize) (by scalar_tac))
    have he : z = 2#usize := UScalar.eq_of_val_eq (by simpa using hv)
    exact hz.trans (congrArg ok he)
  simp only [if_pos hp,hs,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl
#print axioms zero3

theorem zero4 : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 4#usize =
    ok (.cont (rank,0#u64,3#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hp : 4#usize > 0#usize := by scalar_tac
  have hs : 4#usize - 1#usize = ok 3#usize := by
    obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=4#usize) (y:=1#usize) (by scalar_tac))
    have he : z = 3#usize := UScalar.eq_of_val_eq (by simpa using hv)
    exact hz.trans (congrArg ok he)
  simp only [if_pos hp,hs,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl
#print axioms zero4

theorem zero5 : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 5#usize =
    ok (.cont (rank,0#u64,4#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hp : 5#usize > 0#usize := by scalar_tac
  have hs : 5#usize - 1#usize = ok 4#usize := by
    obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=5#usize) (y:=1#usize) (by scalar_tac))
    have he : z = 4#usize := UScalar.eq_of_val_eq (by simpa using hv)
    exact hz.trans (congrArg ok he)
  simp only [if_pos hp,hs,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl
#print axioms zero5

theorem zero6 : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 6#usize =
    ok (.cont (rank,0#u64,5#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hp : 6#usize > 0#usize := by scalar_tac
  have hs : 6#usize - 1#usize = ok 5#usize := by
    obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=6#usize) (y:=1#usize) (by scalar_tac))
    have he : z = 5#usize := UScalar.eq_of_val_eq (by simpa using hv)
    exact hz.trans (congrArg ok he)
  simp only [if_pos hp,hs,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl
#print axioms zero6

theorem zero7 : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 7#usize =
    ok (.cont (rank,0#u64,6#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hp : 7#usize > 0#usize := by scalar_tac
  have hs : 7#usize - 1#usize = ok 6#usize := by
    obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=7#usize) (y:=1#usize) (by scalar_tac))
    have he : z = 6#usize := UScalar.eq_of_val_eq (by simpa using hv)
    exact hz.trans (congrArg ok he)
  simp only [if_pos hp,hs,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl
#print axioms zero7

theorem zero8 : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 8#usize =
    ok (.cont (rank,0#u64,7#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hp : 8#usize > 0#usize := by scalar_tac
  have hs : 8#usize - 1#usize = ok 7#usize := by
    obtain ⟨z,hz,hv,_⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=8#usize) (y:=1#usize) (by scalar_tac))
    have he : z = 7#usize := UScalar.eq_of_val_eq (by simpa using hv)
    exact hz.trans (congrArg ok he)
  simp only [if_pos hp,hs,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl
#print axioms zero8

theorem stop : AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body quotient 0#u64 0#usize =
    ok (.done (quotient,0#u64)) := by rfl

theorem trace : Run step (rank,0#u64,8#usize) (ok (quotient,0#u64)) := by
  apply Run.step _ _ _ zero8
  apply Run.step _ _ _ zero7
  apply Run.step _ _ _ zero6
  apply Run.step _ _ _ zero5
  apply Run.step _ _ _ zero4
  apply Run.step _ _ _ zero3
  apply Run.step _ _ _ zero2
  apply Run.step _ _ _ writes_quotient
  exact Run.done _ _ stop

theorem indexed : AspisR1Post25Sampler.sampler.qm31_div_pass rank = ok (quotient,0#u32) := by
  have h := sound step _ _ trace
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass AspisR1Post25Sampler.sampler.qm31_div_pass_loop
  change (do
    let (q,r) ← loop step (rank,0#u64,8#usize)
    let d ← lift (UScalar.cast .U32 r)
    ok (q,d)) = _
  rw [h]
  rfl

#print axioms stop
#print axioms trace
#print axioms indexed
end XRp_IndexedTrace
