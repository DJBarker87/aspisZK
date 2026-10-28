import NDO_JFu_Q25InputRest
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem step49 : rest49=JFu_Q25Absorb.B49.input ++ rest50 := by
  have cell : (n97.drop 25) ++ n98 ++ n99=JFu_Q25Absorb.B49.input ++ (n99.drop 25) := by rfl
  simpa only [rest49,rest50,suffix098,suffix099,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix100) cell
#print axioms step49
theorem step50 : rest50=JFu_Q25Absorb.B50.input ++ rest51 := by
  have cell : (n99.drop 25) ++ n100 ++ n101=JFu_Q25Absorb.B50.input ++ (n101.drop 25) := by rfl
  simpa only [rest50,rest51,suffix100,suffix101,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix102) cell
#print axioms step50
theorem step51 : rest51=JFu_Q25Absorb.B51.input ++ rest52 := by
  have cell : (n101.drop 25) ++ n102 ++ n103=JFu_Q25Absorb.B51.input ++ (n103.drop 25) := by rfl
  simpa only [rest51,rest52,suffix102,suffix103,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix104) cell
#print axioms step51
theorem step52 : rest52=JFu_Q25Absorb.B52.input ++ rest53 := by
  have cell : (n103.drop 25) ++ n104 ++ n105=JFu_Q25Absorb.B52.input ++ (n105.drop 25) := by rfl
  simpa only [rest52,rest53,suffix104,suffix105,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix106) cell
#print axioms step52
theorem step53 : rest53=JFu_Q25Absorb.B53.input ++ rest54 := by
  have cell : (n105.drop 25) ++ n106 ++ n107=JFu_Q25Absorb.B53.input ++ (n107.drop 25) := by rfl
  simpa only [rest53,rest54,suffix106,suffix107,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix108) cell
#print axioms step53
theorem step54 : rest54=JFu_Q25Absorb.B54.input ++ rest55 := by
  have cell : (n107.drop 25) ++ n108 ++ n109=JFu_Q25Absorb.B54.input ++ (n109.drop 25) := by rfl
  simpa only [rest54,rest55,suffix108,suffix109,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix110) cell
#print axioms step54
theorem step55 : rest55=JFu_Q25Absorb.B55.input ++ rest56 := by
  have cell : (n109.drop 25) ++ n110 ++ n111=JFu_Q25Absorb.B55.input ++ (n111.drop 25) := by rfl
  simpa only [rest55,rest56,suffix110,suffix111,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix112) cell
#print axioms step55
theorem step56 : rest56=JFu_Q25Absorb.B56.input ++ rest57 := by
  have cell : (n111.drop 25) ++ n112 ++ n113=JFu_Q25Absorb.B56.input ++ (n113.drop 25) := by rfl
  simpa only [rest56,rest57,suffix112,suffix113,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix114) cell
#print axioms step56
end Input
end AspisR1.JFu_Q25Source
