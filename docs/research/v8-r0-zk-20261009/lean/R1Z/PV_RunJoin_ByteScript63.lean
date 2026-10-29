import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RJN_Bytes
import R1Z.PV_RunJoin_ResultPost41
/-! Symbolic append/read composition. Reads remain in source order, including
failure and divergence. This is a Result/value theorem, not an effect-world
interpreter or a permission to reorder native allocations. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ByteScript63
open Aeneas Aeneas.Std Result
inductive Code : Type 1 where
  | done
  | read {T : Type} (r : Result T) (next : T → Code)
  | append (s : Slice U8) (next : Code)

def run : Code → alloc.vec.Vec U8 → Result (alloc.vec.Vec U8)
  | .done,out => ok out
  | .read r next,out => do let a ← r; run (next a) out
  | .append s next,out => do
      let out' ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
      run next out'

/-- A successful source script determines its suffix, and the same script
appends it to every prefix with room. No read-success law is postulated. -/
theorem suffix (code : Code) (initial final : alloc.vec.Vec U8)
    (success : run code initial=ok final) :
    ∃ payload : List U8, final.val=initial.val++payload ∧
      ∀ out : alloc.vec.Vec U8, out.length+payload.length≤Usize.max →
        ∃ next, run code out=ok next ∧ next.val=out.val++payload := by
  induction code generalizing initial final with
  | done =>
    have same : initial=final := Result.ok.inj success
    subst final
    refine ⟨[],by simp,?_⟩
    intro out room
    exact ⟨out,rfl,by simp⟩
  | @read T r next ih =>
    cases r with
    | fail e => cases success
    | div => cases success
    | ok a => exact ih a initial final success
  | append s tail ih =>
    obtain ⟨middle,hmiddle,htail⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    have middleBytes := PV_RJN_Bytes.append_success initial s middle hmiddle
    obtain ⟨payload,finalBytes,tailLaw⟩ := ih middle final htail
    refine ⟨s.val++payload,?_,?_⟩
    · rw [finalBytes,middleBytes,List.append_assoc]
    · intro out room
      have room' : out.length+s.length≤Usize.max := by
        change out.length+(s.val++payload).length≤Usize.max at room
        rw [List.length_append] at room
        change out.length+s.val.length≤Usize.max
        omega
      obtain ⟨middle',hmiddle',middleBytes'⟩ := PV_RunJoin_ByteAppend38.append out s room'
      have remaining : middle'.length+payload.length≤Usize.max := by
        change middle'.val.length+payload.length≤Usize.max
        rw [middleBytes',List.length_append]
        change out.val.length+(s.val++payload).length≤Usize.max at room
        rw [List.length_append] at room
        omega
      obtain ⟨next,hnext,nextBytes⟩ := tailLaw middle' remaining
      refine ⟨next,?_,?_⟩
      · simp only [run,hmiddle',bind_tc_ok,hnext]
      · rw [nextBytes,middleBytes',List.append_assoc]

#print axioms Code
#print axioms run
#print axioms suffix
end R1Z.PV_RunJoin_ByteScript63
