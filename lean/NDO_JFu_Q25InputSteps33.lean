import NDO_JFu_Q25InputRest
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem step33 : rest33=JFu_Q25Absorb.B33.input ++ rest34 := by
  have cell : (n65.drop 25) ++ n66 ++ n67=JFu_Q25Absorb.B33.input ++ (n67.drop 25) := by rfl
  simpa only [rest33,rest34,suffix066,suffix067,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix068) cell
#print axioms step33
theorem step34 : rest34=JFu_Q25Absorb.B34.input ++ rest35 := by
  have cell : (n67.drop 25) ++ n68 ++ n69=JFu_Q25Absorb.B34.input ++ (n69.drop 25) := by rfl
  simpa only [rest34,rest35,suffix068,suffix069,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix070) cell
#print axioms step34
theorem step35 : rest35=JFu_Q25Absorb.B35.input ++ rest36 := by
  have cell : (n69.drop 25) ++ n70 ++ n71=JFu_Q25Absorb.B35.input ++ (n71.drop 25) := by rfl
  simpa only [rest35,rest36,suffix070,suffix071,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix072) cell
#print axioms step35
theorem step36 : rest36=JFu_Q25Absorb.B36.input ++ rest37 := by
  have cell : (n71.drop 25) ++ n72 ++ n73=JFu_Q25Absorb.B36.input ++ (n73.drop 25) := by rfl
  simpa only [rest36,rest37,suffix072,suffix073,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix074) cell
#print axioms step36
theorem step37 : rest37=JFu_Q25Absorb.B37.input ++ rest38 := by
  have cell : (n73.drop 25) ++ n74 ++ n75=JFu_Q25Absorb.B37.input ++ (n75.drop 25) := by rfl
  simpa only [rest37,rest38,suffix074,suffix075,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix076) cell
#print axioms step37
theorem step38 : rest38=JFu_Q25Absorb.B38.input ++ rest39 := by
  have cell : (n75.drop 25) ++ n76 ++ n77=JFu_Q25Absorb.B38.input ++ (n77.drop 25) := by rfl
  simpa only [rest38,rest39,suffix076,suffix077,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix078) cell
#print axioms step38
theorem step39 : rest39=JFu_Q25Absorb.B39.input ++ rest40 := by
  have cell : (n77.drop 25) ++ n78 ++ n79=JFu_Q25Absorb.B39.input ++ (n79.drop 25) := by rfl
  simpa only [rest39,rest40,suffix078,suffix079,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix080) cell
#print axioms step39
theorem step40 : rest40=JFu_Q25Absorb.B40.input ++ rest41 := by
  have cell : (n79.drop 25) ++ n80 ++ n81=JFu_Q25Absorb.B40.input ++ (n81.drop 25) := by rfl
  simpa only [rest40,rest41,suffix080,suffix081,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix082) cell
#print axioms step40
end Input
end AspisR1.JFu_Q25Source
