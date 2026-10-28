import R1Z.PV_RunJoin_OpeningLoop41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningRow41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_OpeningCell41 PV_RunJoin_OpeningStep41 PV_RunJoin_OpeningLoop41
variable [ExternalTypes]

def baseBytes (p : Nat → W) : List U8 := payload p 4 0 26 ++ piece (p 28) 16
def secureBytes (p : Nat → W) : List U8 := payload p 16 26 2

theorem base_length (p : Nat → W) : (baseBytes p).length=120 := by
  rw [baseBytes,List.length_append,PV_RunJoin_OpeningLoop41.length _ _ _ _ (by decide),
    PV_RunJoin_OpeningCell41.length _ _ (by decide)]

theorem secure_length (p : Nat → W) : (secureBytes p).length=32 := by
  exact PV_RunJoin_OpeningLoop41.length _ _ _ _ (by decide)

/-- The source base opening row retains lanes 0..25 as four bytes each,
then lane 28 as sixteen bytes. -/
theorem base (ops : ExternalFuns) (p : Nat → W) (out : alloc.vec.Vec U8)
    (room : out.length+120≤Usize.max) :
    ∃ next, @prover.append_opening_base_row _ (ProverRwP6BodyCandidate.selected ops)
      out (ProverCommitArray49.array 29#usize p)=.ok next ∧
      next.val=out.val ++ baseBytes p := by
  obtain ⟨mid,hm,hv⟩ := PV_RunJoin_OpeningLoop41.base ops p 26 0#usize out rfl (by omega)
  have hl : mid.length=out.length+104 := by
    change mid.val.length=out.val.length+104
    rw [hv,List.length_append,PV_RunJoin_OpeningLoop41.length _ _ _ _ (by decide)]
  obtain ⟨next,hn,hnv⟩ := PV_RunJoin_OpeningCell41.append ops (p 28) mid 16#usize
    (by decide) (by change mid.length+16≤Usize.max;rw [hl];omega)
  refine ⟨next,?_,?_⟩
  · unfold prover.append_opening_base_row
    rw [hm]
    simp only [bind_tc_ok]
    rw [ProverCommitArray49.index 29#usize p 28#usize (by decide)]
    simp only [bind_tc_ok]
    exact hn
  · rw [hnv,hv,baseBytes,List.append_assoc]
    rfl

theorem secure (ops : ExternalFuns) (p : Nat → W) (out : alloc.vec.Vec U8)
    (room : out.length+32≤Usize.max) :
    ∃ next, @prover.append_opening_secure_row _ (ProverRwP6BodyCandidate.selected ops)
      out (ProverCommitArray49.array 29#usize p)=.ok next ∧
      next.val=out.val ++ secureBytes p :=
  PV_RunJoin_OpeningLoop41.secure ops p 2 26#usize out rfl room
#print axioms base_length
#print axioms secure_length
#print axioms base
#print axioms secure
end R1Z.PV_RunJoin_OpeningRow41
