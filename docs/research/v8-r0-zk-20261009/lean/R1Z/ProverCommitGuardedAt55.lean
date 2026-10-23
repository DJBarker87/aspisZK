import R1Z.ProverCommitGuardedChannels55
import R1Z.ProverCommitNativeNodes55
import AspisR1ProducerRelease47.EncoderGenericAt54
/-! Complete guarded entry points use optimized native square-based nodes.
The encode bridge records the successful coordinate conversions required to
justify the old owner's different pure operation order. -/
set_option autoImplicit false
namespace R1Z.ProverCommitGuardedAt55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47

theorem eval_same {E : Type} (inst : scalar.CodeField E) (h : Nat) (hh : h≤8)
    (height : Usize) (hheight : height.val=h) (c : Slice E) (hc : c.val.length=2^h)
    (j : Usize) (hj : j.val<262144) :
    guarded55.eval_at inst c j height=generic54.eval_at inst c j height := by
  have hrec : ∀ nodes, guarded55.eval_rec inst c 0#usize height nodes=
      generic54.eval_rec inst c 0#usize height nodes :=
    fun nodes => ProverCommitEncoderGuard55.equivalent inst h hh height 0#usize hheight c hc nodes
  rw [guarded55.eval_at,generic54.eval_at,ProverCommitNativeNodes55.nodes_same j hj]
  simp only [hrec]

theorem encode_same {E : Type} (inst : scalar.CodeField E)
    (from_success : ∀ m : U32, m.val<2147483647 → ∃ x, inst.from_m31 m=ok x)
    (c : Array E 1024#usize) (j : Usize) (hj : j.val<262144) :
    guarded55.encode_at inst c j=generic54.encode_at inst c j := by
  obtain ⟨point,hpoint,hcpoint,hdpoint⟩ := ProverCommitEncoderPoint54.exact_result j
  obtain ⟨xs,hxs,hcxs,hdxs⟩ := ProverCommitEncoderNodes54.exact_result j hj
  obtain ⟨x,hx⟩ := from_success point.a hcpoint.1
  obtain ⟨y,hy⟩ := from_success point.b hcpoint.2
  have hxa : (ProverCommitNativeC49.source point).a=point.a := rfl
  have hya : (ProverCommitNativeC49.source point).b=point.b := rfl
  rw [guarded55.encode_at,generic54.encode_at,ProverCommitNativeGeometry55.point_same,
    ProverCommitNativeNodes55.nodes_same j hj,hpoint,hxs]
  simp only [bind_tc_ok,ProverCommitGuardedChannels55.channels_same,
    generic54.encode_with_nodes,hxa,hya,hx,hy]

#print axioms eval_same
#print axioms encode_same
end R1Z.ProverCommitGuardedAt55
