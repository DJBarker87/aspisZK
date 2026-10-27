import CPH_Program
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_Programs
open Aeneas Aeneas.Std
/-- Default frozen source slot, r1_pool_adapter.rs AUDIT_POOL_PROGRAM fallback.
IDa leaves this slot in missing.adapter; this is an explicit fixture choice. -/
def pool : S2W_ExtractionBoundary.Program := Array.repeat 32#usize 65#u8
def registry : S2W_ExtractionBoundary.Program := Array.repeat 32#usize 68#u8
def foreign : S2W_ExtractionBoundary.Program := Array.repeat 32#usize 85#u8

theorem pool_ne_verifier : pool ≠ CPH_Program.verifier := by
  intro h
  have hd := congrArg (fun k : S2W_ExtractionBoundary.Program => k.val[0]?) h
  change some (65#u8) = some (95#u8) at hd
  exact (by decide : (65#u8) ≠ 95#u8) (Option.some.inj hd)
#print axioms pool_ne_verifier
end AspisR1.JHb_Programs
end
