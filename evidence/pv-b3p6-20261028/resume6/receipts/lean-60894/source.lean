import PV_B3P_SelectLoop227
namespace PV_B3P_SelectValue227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_SelectIndex227 PV_B3P_SelectLoop227
set_option autoImplicit false

def expected (claims : Claims) : List aspis_core.field.QM31 :=
  List.ofFn (fun i : Fin 84 => cell claims i.val i.isLt)

theorem expected_length (claims : Claims) : (expected claims).length = 84 := by
  simp only [expected,List.length_ofFn]

theorem expected_cell (claims : Claims) (i : Nat) (hi : i < 84) :
    (expected claims)[i]'(by simpa only [expected_length] using hi) = cell claims i hi := by
  simp only [expected,List.getElem_ofFn]

theorem prefix_set {α : Type} (out : List α) (i : Nat) (value : α) (hi : i < out.length) :
    (out.set i value).take (i+1) = out.take i ++ [value] := by
  rw [List.take_succ_eq_append_getElem (by simpa using hi),
    List.take_set_of_le (by omega),List.getElem_set_self]

theorem plan_complete (claims : Claims) (n start : Nat) (out : List aspis_core.field.QM31)
    (hs : start+n=84) (hlen : out.length=84)
    (hp : out.take start = (expected claims).take start) :
    plan claims n start out = expected claims := by
  induction n generalizing start out with
  | zero =>
    have he : start=84 := by omega
    have ho : out.take 84 = out := by rw [←hlen,List.take_length]
    have hx : (expected claims).take 84 = expected claims := by
      rw [←expected_length claims,List.take_length]
    simpa only [he,ho,hx,plan] using hp
  | succ n ih =>
    have hb : start<84 := by omega
    simp only [plan,hb,↓reduceDIte]
    apply ih (start+1) (out.set start (cell claims start hb)) (by omega) (by simpa only [List.length_set] using hlen)
    rw [prefix_set out start _ (by omega),hp,
      List.take_succ_eq_append_getElem (by simpa only [expected_length] using hb),expected_cell claims start hb]

theorem complete_value (claims : Claims) :
    observe (reference_terminal.select227 claims) = .ok (expected claims) := by
  rw [complete_result]
  rw [plan_complete claims 84 0 _ (by omega) (by simp only [List.length_replicate]) (by simp only [List.take_zero])]

theorem nonvacuity (claims : Claims) :
    ∃ out, reference_terminal.select227 claims = .ok out ∧ out.val = expected claims := by
  have h := complete_value claims
  cases he : reference_terminal.select227 claims with
  | fail e => simp only [he,observe] at h; cases h
  | div => simp only [he,observe] at h; cases h
  | ok out =>
    refine ⟨out,rfl,?_⟩
    simpa only [he,observe,Result.ok.injEq] using h

#print axioms expected_length
#print axioms expected_cell
#print axioms prefix_set
#print axioms plan_complete
#print axioms complete_value
#print axioms nonvacuity
end PV_B3P_SelectValue227
