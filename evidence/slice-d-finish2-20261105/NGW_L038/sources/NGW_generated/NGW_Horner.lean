import NGW_PolynomialAdd
set_option autoImplicit false
namespace NGW_Horner
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def addE (x y : EW) : EW := (addQ x.1 y.1,addQ x.2 y.2)
def step (a x c : NE) : Result NE := do
 let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul a x
 FIo_Native.aspis_core.field.wide_exact.WideExact.add product c

theorem add_value (x y : NE) (hx : canonE x) (hy : canonE y) :
 ∃ z,FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧ canonE z ∧ ew z=addE (ew x) (ew y) := by
 obtain ⟨a,ha,ca,va⟩ := LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
 obtain ⟨b,hb,cb,vb⟩ := LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
 exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

theorem cell (a x c : NE) (ha : canonE a) (hx : canonE x) (hc : canonE c) :
 ∃ product out,
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul a x=ok product ∧ canonE product ∧
 ew product=mulE (ew a) (ew x) ∧
 NGW_HelperRef.polynomial_step_ref (NGW_PolynomialAdd.words product) (NGW_PolynomialAdd.words c)=ok (NGW_PolynomialAdd.words out) ∧
 step a x c=ok out ∧ canonE out ∧ ew out=addE (mulE (ew a) (ew x)) (ew c) := by
 obtain ⟨product,hp,cp,vp⟩ := LPi_TowerValues.wide_mul a x ha hx
 obtain ⟨out,ho,co,vo⟩ := add_value product c cp hc
 have ref := NGW_PolynomialAdd.observed product c cp hc
 rw [ho] at ref
 simp only [bind_tc_ok] at ref
 exact ⟨product,out,hp,cp,vp,ref,by simp only [step,hp,ho,bind_tc_ok],co,by simpa only [vp] using vo⟩

def walk (x : NE) : List NE → NE → Result NE
 | [],a => ok a
 | c::cs,a => do let next ← step a x c; walk x cs next

theorem induction (x a : NE) (hx : canonE x) (ha : canonE a) (cs : List NE)
 (hc : ∀ c∈cs,canonE c) :
 ∃ out,walk x cs a=ok out ∧ canonE out ∧
 ew out=cs.foldl (fun v c=>addE (mulE v (ew x)) (ew c)) (ew a) := by
 induction cs generalizing a with
 | nil => exact ⟨a,rfl,ha,rfl⟩
 | cons c cs ih =>
  obtain ⟨product,next,_,_,_,_,run,canonical,value⟩ := cell a x c ha hx (hc c (by simp))
  obtain ⟨out,tail,co,vo⟩ := ih next canonical (fun t ht=>hc t (by simp [ht]))
  exact ⟨out,by simp only [walk,run,tail,bind_tc_ok],co,by simpa only [List.foldl_cons,value] using vo⟩

#print axioms add_value
#print axioms cell
#print axioms induction
end NGW_Horner
