import JHb_GuardStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_CheckpointSize
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
/-- Frozen verifier.rs:CHECKPOINT_FIXED + 16*Variant.final_len().
All three variants are included; no successful caller is selected. -/
def value : aspis_r1_cost_probe.transport.Variant → Result Usize
  | .S1 => ok 4840#usize
  | .S2 => ok 1768#usize
  | .D => ok 1768#usize

def install (base : Ops) : Ops := {Hist_Authority.install base with op12:=value}

theorem s2 : value .S2=ok 1768#usize := rfl
#print axioms s2

theorem formula : (16+32*3+64+32*4+16+88+160+64+32*2+16+32)+16*(1024/(2^4))=1768 := by decide
#print axioms formula
end AspisR1.JHb_CheckpointSize
end
