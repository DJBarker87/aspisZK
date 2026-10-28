import NDO_JFu_Q25InputRest
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem step25 : rest25=JFu_Q25Absorb.B25.input ++ rest26 := by
  have cell : (n49.drop 25) ++ n50 ++ n51=JFu_Q25Absorb.B25.input ++ (n51.drop 25) := by rfl
  simpa only [rest25,rest26,suffix050,suffix051,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix052) cell
#print axioms step25
theorem step26 : rest26=JFu_Q25Absorb.B26.input ++ rest27 := by
  have cell : (n51.drop 25) ++ n52 ++ n53=JFu_Q25Absorb.B26.input ++ (n53.drop 25) := by rfl
  simpa only [rest26,rest27,suffix052,suffix053,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix054) cell
#print axioms step26
theorem step27 : rest27=JFu_Q25Absorb.B27.input ++ rest28 := by
  have cell : (n53.drop 25) ++ n54 ++ n55=JFu_Q25Absorb.B27.input ++ (n55.drop 25) := by rfl
  simpa only [rest27,rest28,suffix054,suffix055,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix056) cell
#print axioms step27
theorem step28 : rest28=JFu_Q25Absorb.B28.input ++ rest29 := by
  have cell : (n55.drop 25) ++ n56 ++ n57=JFu_Q25Absorb.B28.input ++ (n57.drop 25) := by rfl
  simpa only [rest28,rest29,suffix056,suffix057,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix058) cell
#print axioms step28
theorem step29 : rest29=JFu_Q25Absorb.B29.input ++ rest30 := by
  have cell : (n57.drop 25) ++ n58 ++ n59=JFu_Q25Absorb.B29.input ++ (n59.drop 25) := by rfl
  simpa only [rest29,rest30,suffix058,suffix059,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix060) cell
#print axioms step29
theorem step30 : rest30=JFu_Q25Absorb.B30.input ++ rest31 := by
  have cell : (n59.drop 25) ++ n60 ++ n61=JFu_Q25Absorb.B30.input ++ (n61.drop 25) := by rfl
  simpa only [rest30,rest31,suffix060,suffix061,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix062) cell
#print axioms step30
theorem step31 : rest31=JFu_Q25Absorb.B31.input ++ rest32 := by
  have cell : (n61.drop 25) ++ n62 ++ n63=JFu_Q25Absorb.B31.input ++ (n63.drop 25) := by rfl
  simpa only [rest31,rest32,suffix062,suffix063,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix064) cell
#print axioms step31
theorem step32 : rest32=JFu_Q25Absorb.B32.input ++ rest33 := by
  have cell : (n63.drop 25) ++ n64 ++ n65=JFu_Q25Absorb.B32.input ++ (n65.drop 25) := by rfl
  simpa only [rest32,rest33,suffix064,suffix065,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix066) cell
#print axioms step32
end Input
end AspisR1.JFu_Q25Source
