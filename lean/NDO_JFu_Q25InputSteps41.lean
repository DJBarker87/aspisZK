import NDO_JFu_Q25InputRest
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem step41 : rest41=JFu_Q25Absorb.B41.input ++ rest42 := by
  have cell : (n81.drop 25) ++ n82 ++ n83=JFu_Q25Absorb.B41.input ++ (n83.drop 25) := by rfl
  simpa only [rest41,rest42,suffix082,suffix083,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix084) cell
#print axioms step41
theorem step42 : rest42=JFu_Q25Absorb.B42.input ++ rest43 := by
  have cell : (n83.drop 25) ++ n84 ++ n85=JFu_Q25Absorb.B42.input ++ (n85.drop 25) := by rfl
  simpa only [rest42,rest43,suffix084,suffix085,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix086) cell
#print axioms step42
theorem step43 : rest43=JFu_Q25Absorb.B43.input ++ rest44 := by
  have cell : (n85.drop 25) ++ n86 ++ n87=JFu_Q25Absorb.B43.input ++ (n87.drop 25) := by rfl
  simpa only [rest43,rest44,suffix086,suffix087,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix088) cell
#print axioms step43
theorem step44 : rest44=JFu_Q25Absorb.B44.input ++ rest45 := by
  have cell : (n87.drop 25) ++ n88 ++ n89=JFu_Q25Absorb.B44.input ++ (n89.drop 25) := by rfl
  simpa only [rest44,rest45,suffix088,suffix089,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix090) cell
#print axioms step44
theorem step45 : rest45=JFu_Q25Absorb.B45.input ++ rest46 := by
  have cell : (n89.drop 25) ++ n90 ++ n91=JFu_Q25Absorb.B45.input ++ (n91.drop 25) := by rfl
  simpa only [rest45,rest46,suffix090,suffix091,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix092) cell
#print axioms step45
theorem step46 : rest46=JFu_Q25Absorb.B46.input ++ rest47 := by
  have cell : (n91.drop 25) ++ n92 ++ n93=JFu_Q25Absorb.B46.input ++ (n93.drop 25) := by rfl
  simpa only [rest46,rest47,suffix092,suffix093,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix094) cell
#print axioms step46
theorem step47 : rest47=JFu_Q25Absorb.B47.input ++ rest48 := by
  have cell : (n93.drop 25) ++ n94 ++ n95=JFu_Q25Absorb.B47.input ++ (n95.drop 25) := by rfl
  simpa only [rest47,rest48,suffix094,suffix095,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix096) cell
#print axioms step47
theorem step48 : rest48=JFu_Q25Absorb.B48.input ++ rest49 := by
  have cell : (n95.drop 25) ++ n96 ++ n97=JFu_Q25Absorb.B48.input ++ (n97.drop 25) := by rfl
  simpa only [rest48,rest49,suffix096,suffix097,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix098) cell
#print axioms step48
end Input
end AspisR1.JFu_Q25Source
