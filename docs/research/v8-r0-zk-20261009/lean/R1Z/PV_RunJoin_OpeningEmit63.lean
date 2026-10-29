import R1Z.PV_RunJoin_QueryScript63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningEmit63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (opening : aspis_core.r0.wire.FibreOpening)
    (out : alloc.vec.Vec U8) (room : out.length+608≤Usize.max) :
    @prover.append_opening_values (types base) (selected base heap box ops) out opening=
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (PV_RunJoin_QueryScript63.openingSlice opening) := by
  obtain ⟨next,hn,hv,hlen⟩ := PV_RunJoin_OpeningPrefix63.append base heap box ops opening out room
  obtain ⟨next',hn',hv'⟩ := PV_RunJoin_ByteAppend38.append out
    (PV_RunJoin_QueryScript63.openingSlice opening) (by
      change out.length+(PV_RunJoin_OpeningPrefix63.payload opening).length≤Usize.max
      rw [PV_RunJoin_OpeningPrefix63.length];exact room)
  rw [hn,hn']
  congr 1
  apply Subtype.ext
  exact hv.trans hv'.symm

#print axioms complete
end R1Z.PV_RunJoin_OpeningEmit63
