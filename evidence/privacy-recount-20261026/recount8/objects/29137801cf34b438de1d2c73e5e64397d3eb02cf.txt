import R1Z.PV_RunJoin_OpeningRow41
import R1Z.PV_RunJoin_ArrayEntries41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningValues41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_OpeningStep41 PV_RunJoin_OpeningRow41
variable [ExternalTypes]

def bytes (p : Nat → Nat → W) : List U8 :=
  baseBytes (p 0) ++ baseBytes (p 1) ++ baseBytes (p 2) ++ baseBytes (p 3) ++
  secureBytes (p 0) ++ secureBytes (p 1) ++ secureBytes (p 2) ++ secureBytes (p 3)

theorem length (p : Nat → Nat → W) : (bytes p).length=608 := by
  simp only [bytes,List.length_append,base_length,secure_length]

/-- Complete actual append_opening_values, with four base rows before four
secure rows. Construction/authentication of FibreOpening remains separate. -/
theorem append (ops : ExternalFuns) (p : Nat → Nat → W)
    (opening : aspis_core.r0.wire.FibreOpening)
    (rows : opening.values=ProverCommitArray49.array 4#usize
      (fun i => ProverCommitArray49.array 29#usize (p i)))
    (out : alloc.vec.Vec U8) (room : out.length+608≤Usize.max) :
    ∃ next, @prover.append_opening_values _ (ProverRwP6BodyCandidate.selected ops)
      out opening=.ok next ∧ next.val=out.val ++ bytes p := by
  obtain ⟨b0,h0,v0⟩ := PV_RunJoin_OpeningRow41.base ops (p 0) out (by omega)
  have l0 : b0.length=out.length+120 := by
    change b0.val.length=out.val.length+120
    rw [v0,List.length_append,PV_RunJoin_OpeningRow41.base_length]
  obtain ⟨b1,h1,v1⟩ := PV_RunJoin_OpeningRow41.base ops (p 1) b0 (by omega)
  have l1 : b1.length=b0.length+120 := by
    change b1.val.length=b0.val.length+120
    rw [v1,List.length_append,PV_RunJoin_OpeningRow41.base_length]
  obtain ⟨b2,h2,v2⟩ := PV_RunJoin_OpeningRow41.base ops (p 2) b1 (by omega)
  have l2 : b2.length=b1.length+120 := by
    change b2.val.length=b1.val.length+120
    rw [v2,List.length_append,PV_RunJoin_OpeningRow41.base_length]
  obtain ⟨b3,h3,v3⟩ := PV_RunJoin_OpeningRow41.base ops (p 3) b2 (by omega)
  have l3 : b3.length=b2.length+120 := by
    change b3.val.length=b2.val.length+120
    rw [v3,List.length_append,PV_RunJoin_OpeningRow41.base_length]
  obtain ⟨b4,h4,v4⟩ := PV_RunJoin_OpeningRow41.secure ops (p 0) b3 (by omega)
  have l4 : b4.length=b3.length+32 := by
    change b4.val.length=b3.val.length+32
    rw [v4,List.length_append,PV_RunJoin_OpeningRow41.secure_length]
  obtain ⟨b5,h5,v5⟩ := PV_RunJoin_OpeningRow41.secure ops (p 1) b4 (by omega)
  have l5 : b5.length=b4.length+32 := by
    change b5.val.length=b4.val.length+32
    rw [v5,List.length_append,PV_RunJoin_OpeningRow41.secure_length]
  obtain ⟨b6,h6,v6⟩ := PV_RunJoin_OpeningRow41.secure ops (p 2) b5 (by omega)
  have l6 : b6.length=b5.length+32 := by
    change b6.val.length=b5.val.length+32
    rw [v6,List.length_append,PV_RunJoin_OpeningRow41.secure_length]
  obtain ⟨b7,h7,v7⟩ := PV_RunJoin_OpeningRow41.secure ops (p 3) b6 (by omega)
  have l7 : b7.length=b6.length+32 := by
    change b7.val.length=b6.val.length+32
    rw [v7,List.length_append,PV_RunJoin_OpeningRow41.secure_length]
  refine ⟨b7,?_,?_⟩
  · unfold prover.append_opening_values
    rw [rows]
    rw [ProverCommitArray49.index 4#usize _ 0#usize (by decide)]
    simp only [bind_tc_ok,show (0#usize).val=0 from rfl]
    rw [h0]
    simp only [bind_tc_ok]
    rw [ProverCommitArray49.index 4#usize _ 1#usize (by decide)]
    simp only [bind_tc_ok,show (1#usize).val=1 from rfl]
    rw [h1]
    simp only [bind_tc_ok]
    rw [ProverCommitArray49.index 4#usize _ 2#usize (by decide)]
    simp only [bind_tc_ok,show (2#usize).val=2 from rfl]
    rw [h2]
    simp only [bind_tc_ok]
    rw [ProverCommitArray49.index 4#usize _ 3#usize (by decide)]
    simp only [bind_tc_ok,show (3#usize).val=3 from rfl]
    rw [h3]
    simp only [bind_tc_ok]
    rw [h4]
    simp only [bind_tc_ok]
    rw [h5]
    simp only [bind_tc_ok]
    rw [h6]
    simp only [bind_tc_ok]
    exact h7
  · rw [v7,v6,v5,v4,v3,v2,v1,v0]
    simp only [bytes,List.append_assoc]

/-- Every actual FibreOpening admits this functional row representation.
No opening-success or byte-equality hypothesis is retained. -/
theorem complete (ops : ExternalFuns) (opening : aspis_core.r0.wire.FibreOpening)
    (out : alloc.vec.Vec U8) (room : out.length+608≤Usize.max) :
    ∃ p next, @prover.append_opening_values _ (ProverRwP6BodyCandidate.selected ops)
      out opening=.ok next ∧ next.val=out.val ++ bytes p ∧ next.length=out.length+608 := by
  let zero : W := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
  let row := PV_RunJoin_ArrayEntries41.entries opening.values (Array.repeat 29#usize zero)
  let p := fun i => PV_RunJoin_ArrayEntries41.entries (row i) zero
  have rows : opening.values=ProverCommitArray49.array 4#usize
      (fun i => ProverCommitArray49.array 29#usize (p i)) := by
    have h : (fun i => ProverCommitArray49.array 29#usize (p i))=row := by
      funext i
      exact PV_RunJoin_ArrayEntries41.rebuild (row i) zero
    rw [h]
    exact (PV_RunJoin_ArrayEntries41.rebuild opening.values (Array.repeat 29#usize zero)).symm
  obtain ⟨next,hn,hv⟩ := append ops p opening rows out room
  refine ⟨p,next,hn,hv,?_⟩
  change next.val.length=out.val.length+608
  rw [hv,List.length_append,length]
#print axioms length
#print axioms append
#print axioms complete
end R1Z.PV_RunJoin_OpeningValues41
