import NGW_ConstructorCM
set_option autoImplicit false
namespace NGW_ConstructorQM
open Aeneas Aeneas.Std Result
abbrev Q := FIn_WeightsExtract.field.QM31

def Canon (x : Q) : Prop := NGW_ConstructorCM.Canon x.c0 ∧ NGW_ConstructorCM.Canon x.c1

theorem add (x y : Q) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.QM31.add x y=ok z ∧ Canon z := by
  obtain ⟨a,ha,ca⟩ := NGW_ConstructorCM.add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb⟩ := NGW_ConstructorCM.add x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIn_WeightsExtract.field.QM31.add,ha,hb,bind_tc_ok],⟨ca,cb⟩⟩

theorem sub (x y : Q) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.QM31.sub x y=ok z ∧ Canon z := by
  obtain ⟨a,ha,ca⟩ := NGW_ConstructorCM.sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb⟩ := NGW_ConstructorCM.sub x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIn_WeightsExtract.field.QM31.sub,ha,hb,bind_tc_ok],⟨ca,cb⟩⟩

theorem mul (x y : Q) (hx : Canon x) (hy : Canon y) :
    ∃ z,FIn_WeightsExtract.field.QM31.mul x y=ok z ∧ Canon z := by
  obtain ⟨ac,hac,cac⟩ := NGW_ConstructorCM.mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd⟩ := NGW_ConstructorCM.mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca⟩ := NGW_ConstructorCM.add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb⟩ := NGW_ConstructorCM.add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross⟩ := NGW_ConstructorCM.mul a b ca cb
  obtain ⟨r,hr,cr⟩ := NGW_ConstructorCM.by_r bd cbd
  obtain ⟨lo,hlo,clo⟩ := NGW_ConstructorCM.add ac r cac cr
  obtain ⟨diff,hdiff,cdiff⟩ := NGW_ConstructorCM.sub cross ac ccross cac
  obtain ⟨hi,hhi,chi⟩ := NGW_ConstructorCM.sub diff bd cdiff cbd
  exact ⟨⟨lo,hi⟩,by simp only [FIn_WeightsExtract.field.QM31.mul,
    hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok],⟨clo,chi⟩⟩

theorem one : Canon FIn_WeightsExtract.field.QM31.ONE := by
  simp [Canon,NGW_ConstructorCM.Canon,FIn_WeightsExtract.field.QM31.ONE]

theorem zero : Canon FIn_WeightsExtract.field.QM31.ZERO := by
  simp [Canon,NGW_ConstructorCM.Canon,FIn_WeightsExtract.field.QM31.ZERO]

theorem double (x : Q) (hx : Canon x) : ∃ z,FIn_WeightsExtract.double x=ok z ∧ Canon z := by
  obtain ⟨a,ha,ca⟩ := mul x x hx hx
  obtain ⟨b,hb,cb⟩ := add a a ca ca
  obtain ⟨z,hz,cz⟩ := sub b FIn_WeightsExtract.field.QM31.ONE cb one
  exact ⟨z,by simp only [FIn_WeightsExtract.double,ha,hb,hz,bind_tc_ok],cz⟩

#print axioms add
#print axioms sub
#print axioms mul
#print axioms one
#print axioms zero
#print axioms double
end NGW_ConstructorQM
