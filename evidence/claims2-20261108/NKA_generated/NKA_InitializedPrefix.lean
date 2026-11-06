import NJT_ClaimsWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_InitializedPrefix
open Aeneas Aeneas.Std
abbrev Memory := Nat → U32
abbrev Rows := Fin 3 → Fin 116 → U32
abbrev Native := Fin 3 → (Fin 116 → U32) → Memory → Memory

def Prefix (rows : Rows) (p : Nat) (memory : Memory) : Prop :=
 ∀ (q : Fin 3) (i : Fin 116),q.val<p → memory (116*q.val+i.val)=rows q i

/-- Precisely the successful arm of NJM_K011/K012 and NJG's result/frame
windows. Only initialized prior rows are observed; the uninitialized suffix
is unrestricted. All calls receive the SAME decoded row. -/
def Cut (native : Native) : Prop :=
 ∀ (p : Fin 3) (row : Fin 116 → U32) (before : Memory),
 (∀ i : Fin 116,native p row before (116*p.val+i.val)=row i) ∧
 (∀ (q : Fin 3) (i : Fin 116),q.val<p.val →
  native p row before (116*q.val+i.val)=before (116*q.val+i.val))

theorem step (native : Native) (cut : Cut native) (rows : Rows)
 (p : Fin 3) (before : Memory) (initialized : Prefix rows p.val before) :
 Prefix rows (p.val+1) (native p (rows p) before) := by
 intro q i bound
 by_cases same : q=p
 · subst q;exact (cut p (rows p) before).1 i
 · have prior : q.val<p.val := by
    have ne : q.val≠p.val := fun eq=>same (Fin.ext eq)
    omega
   exact ((cut p (rows p) before).2 q i prior).trans (initialized q i prior)

def run (native : Native) (rows : Rows) (before : Memory) : Memory :=
 native 2 (rows 2) (native 1 (rows 1) (native 0 (rows 0) before))

/-- Three source writes, each ONE native iteration on arbitrary pre-state,
compose to full initializedness before assume_init. No zero-initialized heap
or endpoint equation occurs in the hypotheses. -/
theorem complete (native : Native) (cut : Cut native) (rows : Rows) (before : Memory) :
 Prefix rows 3 (run native rows before) := by
 have empty : Prefix rows 0 before := by intro q i bound;omega
 have first:=step native cut rows 0 before empty
 have second:=step native cut rows 1 _ first
 exact step native cut rows 2 _ second

theorem window (native : Native) (cut : Cut native) (rows : Rows) (before : Memory)
 (p : Fin 3) (i : Fin 116) : run native rows before (116*p.val+i.val)=rows p i :=
 complete native cut rows before p i p.isLt

#print axioms step
#print axioms complete
#print axioms window
end AspisR1.NKA_InitializedPrefix
end
