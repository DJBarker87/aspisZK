import NLZ_Subwindow
set_option autoImplicit false
namespace AspisR1.NLZ_Geometry137
/-- Frozen parse-record framing. Root occupies bytes0..32; each record includes
its five framing bytes, not only the payload. -/
def offset (j : Nat) : Nat :=
 if j=0 then 32 else if j=1 then 37 else if j=2 then 42 else
 if j<15 then 64+5*j else if j<26 then 171+901*(j-15) else 12898
def width (j : Nat) : Nat :=
 if j=2 ∨ j=14 then 37 else if j<15 then 5 else if j<25 then 901 else
 if j=25 then 3717 else 933
theorem within (j : Nat) (row : j<27) : offset j + width j ≤ 13831 := by
 simp only [offset,width]
 split_ifs <;> omega
theorem consecutive (j : Nat) (row : j<26) : offset (j+1)=offset j+width j := by
 interval_cases j <;> norm_num [offset,width]
theorem first : offset 0=32 := by norm_num [offset]
theorem final : offset 26+width 26=13831 := by norm_num [offset,width]
#print axioms within
#print axioms consecutive
#print axioms first
#print axioms final
end AspisR1.NLZ_Geometry137
