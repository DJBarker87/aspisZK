import NDO_JFu_Q25InputRest
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem step17 : rest17=JFu_Q25Absorb.B17.input ++ rest18 := by
  have cell : (n33.drop 25) ++ n34 ++ n35=JFu_Q25Absorb.B17.input ++ (n35.drop 25) := by rfl
  simpa only [rest17,rest18,suffix034,suffix035,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix036) cell
#print axioms step17
theorem step18 : rest18=JFu_Q25Absorb.B18.input ++ rest19 := by
  have cell : (n35.drop 25) ++ n36 ++ n37=JFu_Q25Absorb.B18.input ++ (n37.drop 25) := by rfl
  simpa only [rest18,rest19,suffix036,suffix037,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix038) cell
#print axioms step18
theorem step19 : rest19=JFu_Q25Absorb.B19.input ++ rest20 := by
  have cell : (n37.drop 25) ++ n38 ++ n39=JFu_Q25Absorb.B19.input ++ (n39.drop 25) := by rfl
  simpa only [rest19,rest20,suffix038,suffix039,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix040) cell
#print axioms step19
theorem step20 : rest20=JFu_Q25Absorb.B20.input ++ rest21 := by
  have cell : (n39.drop 25) ++ n40 ++ n41=JFu_Q25Absorb.B20.input ++ (n41.drop 25) := by rfl
  simpa only [rest20,rest21,suffix040,suffix041,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix042) cell
#print axioms step20
theorem step21 : rest21=JFu_Q25Absorb.B21.input ++ rest22 := by
  have cell : (n41.drop 25) ++ n42 ++ n43=JFu_Q25Absorb.B21.input ++ (n43.drop 25) := by rfl
  simpa only [rest21,rest22,suffix042,suffix043,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix044) cell
#print axioms step21
theorem step22 : rest22=JFu_Q25Absorb.B22.input ++ rest23 := by
  have cell : (n43.drop 25) ++ n44 ++ n45=JFu_Q25Absorb.B22.input ++ (n45.drop 25) := by rfl
  simpa only [rest22,rest23,suffix044,suffix045,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix046) cell
#print axioms step22
theorem step23 : rest23=JFu_Q25Absorb.B23.input ++ rest24 := by
  have cell : (n45.drop 25) ++ n46 ++ n47=JFu_Q25Absorb.B23.input ++ (n47.drop 25) := by rfl
  simpa only [rest23,rest24,suffix046,suffix047,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix048) cell
#print axioms step23
theorem step24 : rest24=JFu_Q25Absorb.B24.input ++ rest25 := by
  have cell : (n47.drop 25) ++ n48 ++ n49=JFu_Q25Absorb.B24.input ++ (n49.drop 25) := by rfl
  simpa only [rest24,rest25,suffix048,suffix049,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix050) cell
#print axioms step24
end Input
end AspisR1.JFu_Q25Source
