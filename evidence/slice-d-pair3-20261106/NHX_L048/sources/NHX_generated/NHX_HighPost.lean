import NHM_ArrayPreserve
import NHX_HighReference
set_option autoImplicit false
namespace NHX_HighPost
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NHX_HighReference

def Canon (parts : Parts) : Prop := ∀ x∈parts.val,canonE x

def Frame (before after : Parts) : Prop :=
 ∀ j:Nat,j≠1→j≠3→after.val[j]?=before.val[j]?

theorem put_canonical (parts : Parts) (i : Usize) (small : i.val<7) (x : NE)
 (hp : Canon parts) (hx : canonE x) : Canon (NHI_ArrayCells.put parts i x) :=
 NHM_ArrayPreserve.canonical canonE parts _ i x hp hx (NHI_ArrayCells.update parts i x small)

theorem first_frame (parts : Parts) (x : NE) : Frame parts (NHI_ArrayCells.put parts 1#usize x) := by
 intro j h1 h3
 exact NHI_ArrayCells.frame parts 1#usize x j h1

theorem second_frame (parts : Parts) (x y : NE) :
 Frame parts (NHI_ArrayCells.put (NHI_ArrayCells.put parts 1#usize x) 3#usize y) := by
 intro j h1 h3
 rw [NHI_ArrayCells.frame _ 3#usize y j h3,NHI_ArrayCells.frame parts 1#usize x j h1]

/-- Includes both error terminals. The SAME scalar inputs and high-dot replies
produce canonical writes; every other part remains the original value. -/
theorem post (partials : Powers) (w : W) (ap0 ap1 : Powers) (parts after : Parts)
 (hf : NHX_HighDomain.Factors w) (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x)
 (hp : Canon parts) (reply : Reply)
 (run : reference partials w ap0 ap1 parts=ok (reply,after)) : Canon after ∧ Frame parts after := by
 have hr0:∀ d (hd:d<5),NHI_CellCanon.array (NHI_ScalarDomain.pick (row0 w) d hd):=hf 0 (by decide)
 have hr2:∀ d (hd:d<5),NHI_CellCanon.array (NHI_ScalarDomain.pick (row2 w) d hd):=hf 2 (by decide)
 obtain ⟨s0,hs0,cs0⟩:=scale_total (row0 w) ap0 ap1 hr0 ha hb
 obtain ⟨s2,hs2,cs2⟩:=scale_total (row2 w) ap0 ap1 hr2 ha hb
 unfold reference at run
 cases hh0:NHM_HighDot.reference partials (coeff0 w) with
 | fail e=>simp only [hh0] at run;cases run
 | div=>simp only [hh0] at run;cases run
 | ok r0=>
  cases r0 with
  | Err e=>
   simp only [hh0,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,lift] at run
   obtain ⟨_,same⟩:=Prod.mk.inj (Result.ok.inj run)
   subst after
   exact ⟨hp,fun _ _ _=>rfl⟩
  | Ok x0=>
   have cx0:=NHX_HighDomain.high_reply partials (coeff0 w) x0 hh0
   obtain ⟨v1,hv1,cv1,_⟩:=LPi_TowerValues.wide_mul s0 x0 cs0 cx0
   simp only [hh0,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,hs0,hv1] at run
   have cp1:=put_canonical parts 1#usize (by decide) v1 hp cv1
   cases hh2:NHM_HighDot.reference partials (coeff2 w) with
   | fail e=>simp only [hh2] at run;cases run
   | div=>simp only [hh2] at run;cases run
   | ok r2=>
    cases r2 with
    | Err e=>
     simp only [hh2,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame,lift] at run
     obtain ⟨_,same⟩:=Prod.mk.inj (Result.ok.inj run)
     subst after
     exact ⟨cp1,first_frame parts v1⟩
    | Ok x2=>
     have cx2:=NHX_HighDomain.high_reply partials (coeff2 w) x2 hh2
     obtain ⟨v3,hv3,cv3,_⟩:=LPi_TowerValues.wide_mul s2 x2 cs2 cx2
     simp only [hh2,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,hs2,hv3] at run
     obtain ⟨_,same⟩:=Prod.mk.inj (Result.ok.inj run)
     subst after
     exact ⟨put_canonical _ 3#usize (by decide) v3 cp1 cv3,second_frame parts v1 v3⟩

#print axioms put_canonical
#print axioms first_frame
#print axioms second_frame
#print axioms post
end NHX_HighPost
