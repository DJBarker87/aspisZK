import NNG_SelectAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_AdmittedAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem three {A : Type} (xs : List A) (length : xs.length=3) :
 ∃ p pub ck,xs=[p,pub,ck] := by
 cases xs with
 | nil=>simp at length
 | cons p xs=>
  cases xs with
  | nil=>simp at length
  | cons pub xs=>
   cases xs with
   | nil=>simp at length
   | cons ck xs=>
    cases xs with
    | nil=>exact ⟨p,pub,ck,rfl⟩
    | cons fourth rest=>simp only [List.length_cons] at length;omega
#print axioms three

theorem count {W : Type} (s : Parent W) :
 (Slice.len s.accounts !=3#usize)=((NNG_ProjectFrames345.original s).accounts.length !=3) := by
 rw [NNG_ReturnAssociation345.compare]
 change (s.accounts.val.length !=3)=((s.accounts.val.map account).length !=3)
 rw [List.length_map]
#print axioms count

theorem source {W : Type} (s : Parent W) (env : RSL.Env)
 (good : s.data.val=[3#u8,10#u8] ∨ s.data.val=[3#u8,11#u8]) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_Tree345.admitted (NNG_Calls345.calls env) s)=
 NNG_Model345.interpretation (NNG_ProjectFrames345.original s) env := by
 have route : s.data.val.length=2 := by rcases good with h|h <;> rw [h] <;> rfl
 have hostRoute : ((NNG_ProjectFrames345.original s).data ==[3,10] ||
   (NNG_ProjectFrames345.original s).data ==[3,11])=true := by
  change ((LIB_Carriers.bytes s.data)==[3,10] || (LIB_Carriers.bytes s.data)==[3,11])=true
  rw [← NNG_DecoderGraph345.bytes]
  rcases good with h|h <;> rw [h] <;> rfl
 unfold NNG_Tree345.admitted NNG_Model345.interpretation NNG_Phases345.run
 rw [count]
 by_cases length : s.accounts.val.length=3
 · have countEq : (NNG_ProjectFrames345.original s).accounts.length=3 := by
    change (s.accounts.val.map account).length=3
    rw [List.length_map,length]
   have bad : RSL.TX1_345.badRoute (NNG_ProjectFrames345.original s)=false := by
    unfold RSL.TX1_345.badRoute
    rw [hostRoute,countEq]
    rfl
   rw [bad]
   simp only [countEq,bne_self_eq_false,Bool.false_eq_true,if_false]
   obtain ⟨p,pub,ck,accounts⟩ := three s.accounts.val length
   have mapped : (NNG_ProjectFrames345.original s).accounts=[account p,account pub,account ck] := by
    change s.accounts.val.map account=_
    rw [accounts]
    rfl
   rw [mapped]
   exact NNG_SelectAssociation345.source s env p pub ck accounts route
 · have countBad : ((NNG_ProjectFrames345.original s).accounts.length !=3)=true := by
    change ((s.accounts.val.map account).length !=3)=true
    simp [length]
   have bad : RSL.TX1_345.badRoute (NNG_ProjectFrames345.original s)=true := by
    unfold RSL.TX1_345.badRoute
    rw [countBad]
    exact Bool.or_true _
   rw [bad,countBad]
   rfl
#print axioms source
end AspisR1.NNG_AdmittedAssociation345
