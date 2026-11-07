import NMX_R2_PrimitiveInstall
import NMX_R2_CloneNative
set_option autoImplicit false
noncomputable section
namespace NMX_R2_StdOps
open Aeneas Aeneas.Std AdapterRw
/-- Unused opaque slots are explicit failures. The source-command semantics
never dispatches CLOSED/OPEN children through these defaults. -/
def unused (failure : Error) : Ops :=
 {
  op0 := by intros; exact .fail failure,
  op1 := by intros; exact .fail failure,
  op2 := by intros; exact .fail failure,
  op3 := by intros; exact .fail failure,
  op4 := by intros; exact .fail failure,
  op5 := by intros; exact .fail failure,
  op6 := by intros; exact .fail failure,
  op7 := by intros; exact .fail failure,
  op8 := by intros; exact .fail failure,
  op9 := by intros; exact .fail failure,
  op10 := by intros; exact .fail failure,
  op11 := by intros; exact .fail failure,
  op12 := by intros; exact .fail failure,
  op13 := by intros; exact .fail failure,
  op14 := by intros; exact .fail failure,
  op15 := by intros; exact .fail failure,
  op16 := by intros; exact .fail failure,
  op17 := by intros; exact .fail failure,
  op18 := by intros; exact .fail failure,
  op19 := by intros; exact .fail failure,
  op20 := by intros; exact .fail failure,
  op21 := by intros; exact .fail failure,
  op22 := by intros; exact .fail failure,
  op23 := by intros; exact .fail failure,
  op24 := by intros; exact .fail failure,
  op25 := by intros; exact .fail failure,
  op26 := by intros; exact .fail failure,
  op27 := by intros; exact .fail failure,
  op28 := by intros; exact .fail failure,
  op29 := by intros; exact .fail failure,
  op30 := by intros; exact .fail failure,
  op31 := by intros; exact .fail failure,
  op32 := by intros; exact .fail failure,
  op33 := by intros; exact .fail failure,
  op34 := by intros; exact .fail failure,
  op35 := by intros; exact .fail failure,
  op36 := by intros; exact .fail failure,
  op37 := by intros; exact .fail failure,
  op38 := by intros; exact .fail failure,
  op39 := by intros; exact .fail failure,
  op40 := by intros; exact .fail failure,
  op41 := by intros; exact .fail failure,
  op42 := by intros; exact .fail failure,
  op43 := by intros; exact .fail failure,
  op44 := by intros; exact .fail failure,
  op45 := by intros; exact .fail failure,
  op46 := by intros; exact .fail failure,
  op47 := by intros; exact .fail failure,
  op48 := by intros; exact .fail failure,
  op49 := by intros; exact .fail failure,
  op50 := by intros; exact .fail failure,
  op51 := by intros; exact .fail failure,
  op52 := by intros; exact .fail failure,
  op53 := by intros; exact .fail failure }
/-- Complete std slots for the caller: key/byte conversions, equality, S2
checkpoint size, all-lanes constant, PDA forwarding and allocating error clone.
Child decoder/registry/lane observations are installed at their own typed calls. -/
def install (env : RSL.Env) (aborts : Bool) (failure : Error) : Ops :=
 {NMX_R2_PrimitiveInstall.install (unused failure) env with
  op35 := NMX_R2_CloneNative.clone aborts failure}

theorem clone (env : RSL.Env) (aborts : Bool) (failure : Error)
 (e : solana_program_error.ProgramError) :
 (install env aborts failure).op35 e = NMX_R2_CloneNative.clone aborts failure e := rfl
#print axioms clone
end NMX_R2_StdOps
end
