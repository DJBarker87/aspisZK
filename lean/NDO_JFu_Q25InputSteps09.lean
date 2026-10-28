import NDO_JFu_Q25InputRest
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem step09 : rest09=JFu_Q25Absorb.B09.input ++ rest10 := by
  have cell : (n17.drop 25) ++ n18 ++ n19=JFu_Q25Absorb.B09.input ++ (n19.drop 25) := by rfl
  simpa only [rest09,rest10,suffix018,suffix019,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix020) cell
#print axioms step09
theorem step10 : rest10=JFu_Q25Absorb.B10.input ++ rest11 := by
  have cell : (n19.drop 25) ++ n20 ++ n21=JFu_Q25Absorb.B10.input ++ (n21.drop 25) := by rfl
  simpa only [rest10,rest11,suffix020,suffix021,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix022) cell
#print axioms step10
theorem step11 : rest11=JFu_Q25Absorb.B11.input ++ rest12 := by
  have cell : (n21.drop 25) ++ n22 ++ n23=JFu_Q25Absorb.B11.input ++ (n23.drop 25) := by rfl
  simpa only [rest11,rest12,suffix022,suffix023,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix024) cell
#print axioms step11
theorem step12 : rest12=JFu_Q25Absorb.B12.input ++ rest13 := by
  have cell : (n23.drop 25) ++ n24 ++ n25=JFu_Q25Absorb.B12.input ++ (n25.drop 25) := by rfl
  simpa only [rest12,rest13,suffix024,suffix025,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix026) cell
#print axioms step12
theorem step13 : rest13=JFu_Q25Absorb.B13.input ++ rest14 := by
  have cell : (n25.drop 25) ++ n26 ++ n27=JFu_Q25Absorb.B13.input ++ (n27.drop 25) := by rfl
  simpa only [rest13,rest14,suffix026,suffix027,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix028) cell
#print axioms step13
theorem step14 : rest14=JFu_Q25Absorb.B14.input ++ rest15 := by
  have cell : (n27.drop 25) ++ n28 ++ n29=JFu_Q25Absorb.B14.input ++ (n29.drop 25) := by rfl
  simpa only [rest14,rest15,suffix028,suffix029,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix030) cell
#print axioms step14
theorem step15 : rest15=JFu_Q25Absorb.B15.input ++ rest16 := by
  have cell : (n29.drop 25) ++ n30 ++ n31=JFu_Q25Absorb.B15.input ++ (n31.drop 25) := by rfl
  simpa only [rest15,rest16,suffix030,suffix031,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix032) cell
#print axioms step15
theorem step16 : rest16=JFu_Q25Absorb.B16.input ++ rest17 := by
  have cell : (n31.drop 25) ++ n32 ++ n33=JFu_Q25Absorb.B16.input ++ (n33.drop 25) := by rfl
  simpa only [rest16,rest17,suffix032,suffix033,List.append_assoc] using
    congrArg (fun t : List Nat => t ++ suffix034) cell
#print axioms step16
end Input
end AspisR1.JFu_Q25Source
