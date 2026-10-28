import NDO_JFu_Q25InputRest
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem step01 : rest01=JFu_Q25Absorb.B01.input ++ rest02 := by
  have cell : (n01.drop 25) ++ n02 ++ n03=JFu_Q25Absorb.B01.input ++ (n03.drop 25) := by rfl
  simpa only [rest01,rest02,suffix002,suffix003,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix004) cell
#print axioms step01
theorem step02 : rest02=JFu_Q25Absorb.B02.input ++ rest03 := by
  have cell : (n03.drop 25) ++ n04 ++ n05=JFu_Q25Absorb.B02.input ++ (n05.drop 25) := by rfl
  simpa only [rest02,rest03,suffix004,suffix005,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix006) cell
#print axioms step02
theorem step03 : rest03=JFu_Q25Absorb.B03.input ++ rest04 := by
  have cell : (n05.drop 25) ++ n06 ++ n07=JFu_Q25Absorb.B03.input ++ (n07.drop 25) := by rfl
  simpa only [rest03,rest04,suffix006,suffix007,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix008) cell
#print axioms step03
theorem step04 : rest04=JFu_Q25Absorb.B04.input ++ rest05 := by
  have cell : (n07.drop 25) ++ n08 ++ n09=JFu_Q25Absorb.B04.input ++ (n09.drop 25) := by rfl
  simpa only [rest04,rest05,suffix008,suffix009,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix010) cell
#print axioms step04
theorem step05 : rest05=JFu_Q25Absorb.B05.input ++ rest06 := by
  have cell : (n09.drop 25) ++ n10 ++ n11=JFu_Q25Absorb.B05.input ++ (n11.drop 25) := by rfl
  simpa only [rest05,rest06,suffix010,suffix011,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix012) cell
#print axioms step05
theorem step06 : rest06=JFu_Q25Absorb.B06.input ++ rest07 := by
  have cell : (n11.drop 25) ++ n12 ++ n13=JFu_Q25Absorb.B06.input ++ (n13.drop 25) := by rfl
  simpa only [rest06,rest07,suffix012,suffix013,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix014) cell
#print axioms step06
theorem step07 : rest07=JFu_Q25Absorb.B07.input ++ rest08 := by
  have cell : (n13.drop 25) ++ n14 ++ n15=JFu_Q25Absorb.B07.input ++ (n15.drop 25) := by rfl
  simpa only [rest07,rest08,suffix014,suffix015,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix016) cell
#print axioms step07
theorem step08 : rest08=JFu_Q25Absorb.B08.input ++ rest09 := by
  have cell : (n15.drop 25) ++ n16 ++ n17=JFu_Q25Absorb.B08.input ++ (n17.drop 25) := by rfl
  simpa only [rest08,rest09,suffix016,suffix017,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix018) cell
#print axioms step08
end Input
end AspisR1.JFu_Q25Source
