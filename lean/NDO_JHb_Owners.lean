import NDO_JHb_World
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_Owners
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHb_World

theorem master : (e2.snapshot 1 384 384).owner=JHb_Programs.pool := rfl
#print axioms master
theorem forest : (e2.snapshot 2 192 192).owner=JHb_Programs.pool := rfl
#print axioms forest
theorem lane : (e2.snapshot 3 768 768).owner=JHb_Programs.pool := rfl
#print axioms lane
theorem registry : (e2.snapshot 4 128 256).owner=JHb_Programs.registry := rfl
#print axioms registry
theorem entry : (e2.snapshot 5 192 320).owner=JHb_Programs.registry := rfl
#print axioms entry
theorem checkpoint : (e2.snapshot 6 1768 1768).owner=CPH_Program.verifier := rfl
#print axioms checkpoint
theorem tx1_checkpoint : (e1.snapshot 2 1768 1768).owner=CPH_Program.verifier := rfl
#print axioms tx1_checkpoint
theorem proof : (e2.snapshot 0 58295 58295).owner=JHb_Programs.foreign := rfl
#print axioms proof
end AspisR1.JHb_Owners
end
