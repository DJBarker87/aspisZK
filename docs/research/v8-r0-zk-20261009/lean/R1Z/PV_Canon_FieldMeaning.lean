import R1Z.PV_Canon_Carrier
import R1Z.PV_CurrentQuarticBridge
import R1Z.ProverRw18FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Raw := ProverRw18FieldMeaning.Raw
abbrev K := ProverRw18FieldMeaning.K
def old (x : aspis_core.field.QM31) : Raw := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def decodeQ (x : aspis_core.field.QM31) : K := ProverRw18FieldMeaning.decode (old x)
 theorem full_old (x : aspis_core.field.QM31) : ProverRw18FieldMeaning.full (old x)=x := by
  cases x; rfl
 theorem old_full (x : Raw) : old (ProverRw18FieldMeaning.full x)=x := by
  cases x with | mk a b => cases a; cases b; rfl
 theorem current_qadd_meaning (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add x y = .ok z ∧ Q z ∧ decodeQ z=decodeQ x+decodeQ y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverRw18FieldMeaning.add (old x) (old y) hx hy
  rw [full_old,full_old] at hz
  refine ⟨ProverRw18FieldMeaning.full z,?_,hc,?_⟩
  · change PV_CurrentQuarticBridge.S.add x y = _
    rw [PV_CurrentQuarticBridge.add]; exact hz
  · simpa only [decodeQ,old_full] using hd
 theorem current_qmul_meaning (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul x y = .ok z ∧ Q z ∧ decodeQ z=decodeQ x*decodeQ y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverRw18FieldMeaning.mul (old x) (old y) hx hy
  rw [full_old,full_old] at hz
  refine ⟨ProverRw18FieldMeaning.full z,?_,hc,?_⟩
  · change PV_CurrentQuarticBridge.S.mul x y = _
    rw [PV_CurrentQuarticBridge.mul]; exact hz
  · simpa only [decodeQ,old_full] using hd
#print axioms full_old
#print axioms old_full
#print axioms current_qadd_meaning
#print axioms current_qmul_meaning
end R1Z.PV_Canon
