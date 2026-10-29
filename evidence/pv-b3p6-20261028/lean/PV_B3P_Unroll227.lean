import PV_B3P_Ordered227
namespace PV_B3P_Unroll227
open Aeneas Aeneas.Std PV_B3P_Ordered227
set_option autoImplicit false

theorem forward_3 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 3) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      .ok next2) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_3

theorem forward_4 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 4) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      .ok next3) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_4

theorem forward_7 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 7) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      .ok next6) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_7

theorem forward_8 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 8) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      let next7 ← step next6 (start+7)
      .ok next7) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_8

theorem forward_10 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 10) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      let next7 ← step next6 (start+7)
      let next8 ← step next7 (start+8)
      let next9 ← step next8 (start+9)
      .ok next9) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_10

theorem forward_16 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 16) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      let next7 ← step next6 (start+7)
      let next8 ← step next7 (start+8)
      let next9 ← step next8 (start+9)
      let next10 ← step next9 (start+10)
      let next11 ← step next10 (start+11)
      let next12 ← step next11 (start+12)
      let next13 ← step next12 (start+13)
      let next14 ← step next13 (start+14)
      let next15 ← step next14 (start+15)
      .ok next15) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_16

theorem forward_20 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 20) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      let next7 ← step next6 (start+7)
      let next8 ← step next7 (start+8)
      let next9 ← step next8 (start+9)
      let next10 ← step next9 (start+10)
      let next11 ← step next10 (start+11)
      let next12 ← step next11 (start+12)
      let next13 ← step next12 (start+13)
      let next14 ← step next13 (start+14)
      let next15 ← step next14 (start+15)
      let next16 ← step next15 (start+16)
      let next17 ← step next16 (start+17)
      let next18 ← step next17 (start+18)
      let next19 ← step next18 (start+19)
      .ok next19) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_20

theorem forward_21 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 21) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      let next7 ← step next6 (start+7)
      let next8 ← step next7 (start+8)
      let next9 ← step next8 (start+9)
      let next10 ← step next9 (start+10)
      let next11 ← step next10 (start+11)
      let next12 ← step next11 (start+12)
      let next13 ← step next12 (start+13)
      let next14 ← step next13 (start+14)
      let next15 ← step next14 (start+15)
      let next16 ← step next15 (start+16)
      let next17 ← step next16 (start+17)
      let next18 ← step next17 (start+18)
      let next19 ← step next18 (start+19)
      let next20 ← step next19 (start+20)
      .ok next20) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_21

theorem forward_24 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 24) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      let next7 ← step next6 (start+7)
      let next8 ← step next7 (start+8)
      let next9 ← step next8 (start+9)
      let next10 ← step next9 (start+10)
      let next11 ← step next10 (start+11)
      let next12 ← step next11 (start+12)
      let next13 ← step next12 (start+13)
      let next14 ← step next13 (start+14)
      let next15 ← step next14 (start+15)
      let next16 ← step next15 (start+16)
      let next17 ← step next16 (start+17)
      let next18 ← step next17 (start+18)
      let next19 ← step next18 (start+19)
      let next20 ← step next19 (start+20)
      let next21 ← step next20 (start+21)
      let next22 ← step next21 (start+22)
      let next23 ← step next22 (start+23)
      .ok next23) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_24

theorem forward_33 {α : Type} (step : α → Nat → Result α) (start : Nat) (initial : α) :
    fold step (List.range' start 33) initial = (    do
      let next0 ← step initial (start+0)
      let next1 ← step next0 (start+1)
      let next2 ← step next1 (start+2)
      let next3 ← step next2 (start+3)
      let next4 ← step next3 (start+4)
      let next5 ← step next4 (start+5)
      let next6 ← step next5 (start+6)
      let next7 ← step next6 (start+7)
      let next8 ← step next7 (start+8)
      let next9 ← step next8 (start+9)
      let next10 ← step next9 (start+10)
      let next11 ← step next10 (start+11)
      let next12 ← step next11 (start+12)
      let next13 ← step next12 (start+13)
      let next14 ← step next13 (start+14)
      let next15 ← step next14 (start+15)
      let next16 ← step next15 (start+16)
      let next17 ← step next16 (start+17)
      let next18 ← step next17 (start+18)
      let next19 ← step next18 (start+19)
      let next20 ← step next19 (start+20)
      let next21 ← step next20 (start+21)
      let next22 ← step next21 (start+22)
      let next23 ← step next22 (start+23)
      let next24 ← step next23 (start+24)
      let next25 ← step next24 (start+25)
      let next26 ← step next25 (start+26)
      let next27 ← step next26 (start+27)
      let next28 ← step next27 (start+28)
      let next29 ← step next28 (start+29)
      let next30 ← step next29 (start+30)
      let next31 ← step next30 (start+31)
      let next32 ← step next31 (start+32)
      .ok next32) := by
  simp only [List.range'_succ,fold]
  rfl
#print axioms forward_33

end PV_B3P_Unroll227
