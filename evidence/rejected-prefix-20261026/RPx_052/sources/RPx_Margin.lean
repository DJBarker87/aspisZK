import F3T_Numeric
set_option autoImplicit false
namespace AspisR1.RPx_Margin

/-- The installed-source transport adds no omitted-query loss. -/
theorem unchanged : 1/(2:Rat)^100-F3T_Numeric.total 0 =
    1/(2:Rat)^108-6*((1161:Rat)^2+2965^2)/(2:Rat)^256-
      1/(2:Rat)^126-1/(2:Rat)^454 := F3T_Numeric.margin_exact

/-- Diagnostic for the unrestricted runtime-interface prefix, not a finding
of this many missing shipped-source calls. An unbounded prefix cannot be
absorbed in the frozen zero-query margin: already n=2^74 exceeds it. -/
theorem unrestricted_does_not_fit :
    1/(2:Rat)^108-6*((1161:Rat)^2+2965^2)/(2:Rat)^256-
      1/(2:Rat)^126-1/(2:Rat)^454 <
    6*(((2965:Rat)+2^74)^2-2965^2)/(2:Rat)^256 := by
  have collision : 0≤6*((1161:Rat)^2+2965^2)/(2:Rat)^256 := by positivity
  have abort1 : 0≤1/(2:Rat)^126 := by positivity
  have abort2 : 0≤1/(2:Rat)^454 := by positivity
  have gap : 1/(2:Rat)^108 < 6*(((2965:Rat)+2^74)^2-2965^2)/(2:Rat)^256 := by norm_num
  linarith

#print axioms unchanged
#print axioms unrestricted_does_not_fit
end AspisR1.RPx_Margin
