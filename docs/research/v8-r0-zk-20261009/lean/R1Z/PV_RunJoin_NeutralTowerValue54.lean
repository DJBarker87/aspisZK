import R1Z.PV_RunJoin_NeutralValue54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralTowerValue54
open PV_RunJoin_NeutralValue54 PV_RunJoin_CircleNeutralShape53
abbrev C := U32 × U32
abbrev Q := C × C
abbrev V := M × M
def cv (a : C) : V := (scalar a.1,scalar a.2)
def ca (a b : V) : V := (a.1+b.1,a.2+b.2)
def cs (a b : V) : V := (a.1-b.1,a.2-b.2)
def cm (a b : V) : V := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
def cr (a : V) : V := (2*a.1-a.2,a.1+2*a.2)
def qv (a : Q) : V × V := (cv a.1,cv a.2)
def qm (a b : V × V) : V × V :=
  (ca (cm a.1 b.1) (cr (cm a.2 b.2)),
    cs (cs (cm (ca a.1 a.2) (ca b.1 b.2)) (cm a.1 b.1)) (cm a.2 b.2))
theorem ci (a b : C) (ha : CC a) (hb : CC b) (h : cv a=cv b) : a=b := by
  exact Prod.ext (injective _ _ ha.1 hb.1 (congrArg Prod.fst h))
    (injective _ _ ha.2 hb.2 (congrArg Prod.snd h))
theorem qi (a b : Q) (ha : QC a) (hb : QC b) (h : qv a=qv b) : a=b := by
  exact Prod.ext (ci _ _ ha.1 hb.1 (congrArg Prod.fst h))
    (ci _ _ ha.2 hb.2 (congrArg Prod.snd h))
#print axioms cv
#print axioms ca
#print axioms cs
#print axioms cm
#print axioms cr
#print axioms qv
#print axioms qm
#print axioms ci
#print axioms qi
end R1Z.PV_RunJoin_NeutralTowerValue54
