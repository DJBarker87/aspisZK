import R1Z.PV_RunJoin_OpeningCongruence63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningPrefix63
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
abbrev W := aspis_core.field.wide_exact.WideExact
variable [ExternalTypes]
def zero : W := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def row (opening : aspis_core.r0.wire.FibreOpening) : Nat → Array W 29#usize :=
  PV_RunJoin_ArrayEntries41.entries opening.values (Array.repeat 29#usize zero)
def value (opening : aspis_core.r0.wire.FibreOpening) : Nat → Nat → W :=
  fun i => PV_RunJoin_ArrayEntries41.entries (row opening i) zero
def payload (opening : aspis_core.r0.wire.FibreOpening) : List U8 :=
  PV_RunJoin_OpeningValues41.bytes (value opening)

theorem rows (opening : aspis_core.r0.wire.FibreOpening) :
    opening.values=ProverCommitArray49.array 4#usize
      (fun i => ProverCommitArray49.array 29#usize (value opening i)) := by
  have inner : (fun i => ProverCommitArray49.array 29#usize (value opening i))=row opening := by
    funext i
    exact PV_RunJoin_ArrayEntries41.rebuild (row opening i) zero
  rw [inner]
  exact (PV_RunJoin_ArrayEntries41.rebuild opening.values (Array.repeat 29#usize zero)).symm

theorem length (opening : aspis_core.r0.wire.FibreOpening) : (payload opening).length=608 :=
  PV_RunJoin_OpeningValues41.length _

theorem append (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (opening : aspis_core.r0.wire.FibreOpening)
    (out : alloc.vec.Vec U8) (room : out.length+608≤Usize.max) :
    ∃ next, @prover.append_opening_values (types base) (selected base heap box ops) out opening=ok next ∧
      next.val=out.val++payload opening ∧ next.length=out.length+608 := by
  letI : ExternalTypes := types base
  rw [PV_RunJoin_OpeningCongruence63.complete _ _ (PV_RunJoin_EncodedInstalled48.field base heap box ops)]
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_OpeningValues41.append ops (value opening) opening (rows opening) out room
  refine ⟨next,hn,hv,?_⟩
  change next.val.length=out.val.length+608
  rw [hv,List.length_append,PV_RunJoin_OpeningValues41.length]

#print axioms zero
#print axioms row
#print axioms value
#print axioms payload
#print axioms rows
#print axioms length
#print axioms append
end R1Z.PV_RunJoin_OpeningPrefix63
