from pathlib import Path
root=Path(__file__).resolve().parents[2]
s='''import R1Z.PV_RunJoin_OpeningRow41
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
'''
for i in range(8):
 name='base' if i<4 else 'secure'; width=120 if i<4 else 32;prev='out' if i==0 else f'b{i-1}'
 s+=f'  obtain ⟨b{i},h{i},v{i}⟩ := PV_RunJoin_OpeningRow41.{name} ops (p {i%4}) {prev} (by omega)\n'
 s+=f'''  have l{i} : b{i}.length={prev}.length+{width} := by
    change b{i}.val.length={prev}.val.length+{width}
    rw [v{i},List.length_append,PV_RunJoin_OpeningRow41.{name}_length]
'''
s+='  refine ⟨b7,?_,?_⟩\n  · unfold prover.append_opening_values\n    rw [rows]\n'
for i in range(4):
 s+=f'    rw [ProverCommitArray49.index 4#usize _ {i}#usize (by decide)]\n    simp only [bind_tc_ok,show ({i}#usize).val={i} from rfl]\n    rw [h{i}]\n    simp only [bind_tc_ok]\n'
for i in range(4,7):s+=f'    rw [h{i}]\n    simp only [bind_tc_ok]\n'
s+='    exact h7\n  · rw ['+','.join(f'v{i}' for i in reversed(range(8)))+']\n    simp only [bytes,List.append_assoc]\n'
s+='''
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
'''
(root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_OpeningValues41.lean').write_text(s)
