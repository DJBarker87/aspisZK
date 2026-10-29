import R1Z.PV_OWNO_HelperSelect
import R1Z.PV_OWNL_Inputs
set_option autoImplicit false
namespace R1Z.PV_OWNO_Builder
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNO_HelperArrays

def acceptedBase (base : List (List U32)) : Bool :=
 base.all fun c => decide (c.length = 1024) && c.all (fun x => decide (x.val < 2147483647))

def acceptedExtensions (d g : List Q) : Bool :=
 (d ++ g).all PV_OWNL_InputBytes.checked

/-- Value projection of build_with_helper_mode through column construction.
The setup continuation retains the C1/root/lambda/chi failures; the finish
continuation retains C2/theta/zc/mu failures. No success of either is assumed. -/
def build {E : Type} (publicError imbalance : E) (inverse : Q → Option Q)
 (base : Aeneas.Std.Array (List U32) 26#usize)
 (d g : Aeneas.Std.Array Q 1024#usize)
 (setup : Unit → Except E (Q × Q)) (registry : Q → Except E (List CopyRow))
 (balanced : List Q → Bool) (finish : List Q → Except E Unit) : Except E (List (List Q)) :=
 if acceptedBase base.val && acceptedExtensions d.val g.val then
  match setup () with
  | .error e => .error e
  | .ok (lambda,chi) =>
   match PV_OWNO_HelperSelect.selected imbalance inverse chi (registry lambda) with
   | .error e => .error e
   | .ok h1 =>
    if h1.length ≠ 1024 then .error publicError else
    if balanced h1 then
     match finish h1 with
     | .error e => .error e
     | .ok _ => .ok (base.val.map (List.map PV_OWNL_Inputs.lift) ++ [h1,g.val,d.val])
    else .error publicError
 else .error publicError

theorem base_canonical (base : List (List U32)) (h : acceptedBase base = true) :
 ∀ c ∈ base, ∀ x ∈ c, x.val < 2147483647 := by
 intro c hc x hx
 have hrow := (List.all_eq_true.mp h) c hc
 have hlimbs := (Bool.and_eq_true_iff.mp hrow).2
 exact of_decide_eq_true ((List.all_eq_true.mp hlimbs) x hx)

theorem extensions_canonical (d g : List Q) (h : acceptedExtensions d g = true) :
 (∀ q ∈ d, Canon q) ∧ (∀ q ∈ g, Canon q) := by
 have hall := PV_OWNL_InputBytes.accepted_canonical (d ++ g) h
 exact ⟨fun q hq => hall q (List.mem_append_left _ hq),
  fun q hq => hall q (List.mem_append_right _ hq)⟩

theorem successful_canonical {E : Type} (publicError imbalance : E)
 (inverse : Q → Option Q) (base : Aeneas.Std.Array (List U32) 26#usize)
 (d g : Aeneas.Std.Array Q 1024#usize)
 (setup : Unit → Except E (Q × Q)) (registry : Q → Except E (List CopyRow))
 (balanced : List Q → Bool) (finish : List Q → Except E Unit) (out : List (List Q))
 (h : build publicError imbalance inverse base d g setup registry balanced finish = .ok out) :
 ∀ c ∈ out, ∀ q ∈ c, Canon q := by
 unfold build at h
 split at h
 · rename_i accepted
   have hh := Bool.and_eq_true_iff.mp accepted
   have hb := base_canonical base.val hh.1
   have he := extensions_canonical d.val g.val hh.2
   cases hs : setup () with
   | error e => simp only [hs] at h; cases h
   | ok params =>
    rcases params with ⟨lambda,chi⟩
    simp only [hs] at h
    cases hr : PV_OWNO_HelperSelect.selected imbalance inverse chi (registry lambda) with
    | error e => simp only [hr] at h; cases h
    | ok h1 =>
     simp only [hr] at h
     split at h
     · cases h
     · split at h
       · cases hf : finish h1 with
         | error e => simp only [hf] at h; cases h
         | ok unit =>
          simp only [hf] at h
          cases Except.ok.inj h
          exact PV_OWNL_Inputs.columns_canon base.val h1 g.val d.val hb
           (PV_OWNO_HelperSelect.successful_canonical imbalance inverse chi (registry lambda) h1 hr)
           he.2 he.1
       · cases h
 · cases h

#print axioms base_canonical
#print axioms extensions_canonical
#print axioms successful_canonical
end R1Z.PV_OWNO_Builder
