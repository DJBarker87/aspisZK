import R1Z.PV_RunJoin_NativeWideParse73
import R1Z.PV_RunJoin_PolyCellCanonical72
import R1Z.PV_RunJoin_NativeQuarticEq72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePolyCellParse73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (q : Q) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    aspis_core.field.wide_exact.WideExact.from_le_bytes
      (Array.to_slice (PV_RunJoin_FlatBytes35.wire (PV_RunJoin_PolyCell38.wide q)))=
        ok (some (PV_RunJoin_PolyCell38.wide q)) ∧
    (do let high ← aspis_core.field.wide_exact.WideExact.impl.c1 (PV_RunJoin_PolyCell38.wide q)
        let zero ← aspis_core.field.QM31.ZERO
        core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 high zero)=ok false := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  let zero : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
  have hz : aspis_core.field.QM31.ZERO=ok zero := by
    rw [PV_RunJoin_NativeQuarticTotal69.zero_source base heap box ops runtime world]
    rfl
  have hh : aspis_core.field.wide_exact.WideExact.impl.c1 (PV_RunJoin_PolyCell38.wide q)=ok zero := by
    rw [PV_RunJoin_NativeWideParse73.c1]
    rfl
  refine ⟨PV_RunJoin_NativeWideParse73.complete base heap box ops runtime world
    (PV_RunJoin_PolyCell38.wide q) (PV_RunJoin_PolyCellCanonical72.complete q),?_⟩
  simp only [hh,hz,bind_tc_ok,PV_RunJoin_NativeQuarticEq72.ne_self base heap box ops runtime world]

#print axioms complete
end R1Z.PV_RunJoin_NativePolyCellParse73
