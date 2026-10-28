import NDO_JFu_Q25InputSteps00
import NDO_JFu_Q25InputSteps01
import NDO_JFu_Q25InputSteps09
import NDO_JFu_Q25InputSteps17
import NDO_JFu_Q25InputSteps25
import NDO_JFu_Q25InputSteps33
import NDO_JFu_Q25InputSteps41
import NDO_JFu_Q25InputSteps49
import NDO_JFu_Q25InputSteps57
set_option autoImplicit false
namespace AspisR1.JFu_Q25Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace Input
attribute [local irreducible] suffix000 suffix001 suffix002 suffix003 suffix004 suffix005 suffix006 suffix007 suffix008 suffix009 suffix010 suffix011 suffix012 suffix013 suffix014 suffix015 suffix016 suffix017 suffix018 suffix019 suffix020 suffix021 suffix022 suffix023 suffix024 suffix025 suffix026 suffix027 suffix028 suffix029 suffix030 suffix031 suffix032 suffix033 suffix034 suffix035 suffix036 suffix037 suffix038 suffix039 suffix040 suffix041 suffix042 suffix043 suffix044 suffix045 suffix046 suffix047 suffix048 suffix049 suffix050 suffix051 suffix052 suffix053 suffix054 suffix055 suffix056 suffix057 suffix058 suffix059 suffix060 suffix061 suffix062 suffix063 suffix064 suffix065 suffix066 suffix067 suffix068 suffix069 suffix070 suffix071 suffix072 suffix073 suffix074 suffix075 suffix076 suffix077 suffix078 suffix079 suffix080 suffix081 suffix082 suffix083 suffix084 suffix085 suffix086 suffix087 suffix088 suffix089 suffix090 suffix091 suffix092 suffix093 suffix094 suffix095 suffix096 suffix097 suffix098 suffix099 suffix100 suffix101 suffix102 suffix103 suffix104 suffix105 suffix106 suffix107 suffix108 suffix109 suffix110 suffix111 suffix112 suffix113 suffix114 suffix115 suffix116
theorem last : rest58=JFu_Q25Absorb.tail := by
  simp only [rest58,suffix116,n115,n116]
  rfl
#print axioms last
theorem regroup : numeric=JFu_Q25Absorb.message := by
  rw [numeric_eq]
  change rest00=JFu_Q25Absorb.message
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,step14,step15,step16,step17,step18,step19,step20,step21,step22,step23,step24,step25,step26,step27,step28,step29,step30,step31,step32,step33,step34,step35,step36,step37,step38,step39,step40,step41,step42,step43,step44,step45,step46,step47,step48,step49,step50,step51,step52,step53,step54,step55,step56,step57,last]
  simp only [JFu_Q25Absorb.message,JFu_Q25Absorb.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup
theorem native : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q24Source.ratchet) 185#u8 frame)).map Fin.val=numeric := by
  simp only [flatten,TranscriptStep.absorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,
    List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,frameBytes,payloadNat,List.map_cons,List.map_nil]
  change ((encodeState JFm_Q24Source.ratchet).val.map (fun x=>x.val)) ++ ([0,185] ++ ([4,128,14,0,0] ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64 ++ n65 ++ n66 ++ n67 ++ n68 ++ n69 ++ n70 ++ n71 ++ n72 ++ n73 ++ n74 ++ n75 ++ n76 ++ n77 ++ n78 ++ n79 ++ n80 ++ n81 ++ n82 ++ n83 ++ n84 ++ n85 ++ n86 ++ n87 ++ n88 ++ n89 ++ n90 ++ n91 ++ n92 ++ n93 ++ n94 ++ n95 ++ n96 ++ n97 ++ n98 ++ n99 ++ n100 ++ n101 ++ n102 ++ n103 ++ n104 ++ n105 ++ n106 ++ n107 ++ n108 ++ n109 ++ n110 ++ n111 ++ n112 ++ n113 ++ n114 ++ n115 ++ n116)))=numeric
  have joined := congrArg (fun lead => lead ++ (n01 ++ n02 ++ n03 ++ n04 ++ n05 ++ n06 ++ n07 ++ n08 ++ n09 ++ n10 ++ n11 ++ n12 ++ n13 ++ n14 ++ n15 ++ n16 ++ n17 ++ n18 ++ n19 ++ n20 ++ n21 ++ n22 ++ n23 ++ n24 ++ n25 ++ n26 ++ n27 ++ n28 ++ n29 ++ n30 ++ n31 ++ n32 ++ n33 ++ n34 ++ n35 ++ n36 ++ n37 ++ n38 ++ n39 ++ n40 ++ n41 ++ n42 ++ n43 ++ n44 ++ n45 ++ n46 ++ n47 ++ n48 ++ n49 ++ n50 ++ n51 ++ n52 ++ n53 ++ n54 ++ n55 ++ n56 ++ n57 ++ n58 ++ n59 ++ n60 ++ n61 ++ n62 ++ n63 ++ n64 ++ n65 ++ n66 ++ n67 ++ n68 ++ n69 ++ n70 ++ n71 ++ n72 ++ n73 ++ n74 ++ n75 ++ n76 ++ n77 ++ n78 ++ n79 ++ n80 ++ n81 ++ n82 ++ n83 ++ n84 ++ n85 ++ n86 ++ n87 ++ n88 ++ n89 ++ n90 ++ n91 ++ n92 ++ n93 ++ n94 ++ n95 ++ n96 ++ n97 ++ n98 ++ n99 ++ n100 ++ n101 ++ n102 ++ n103 ++ n104 ++ n105 ++ n106 ++ n107 ++ n108 ++ n109 ++ n110 ++ n111 ++ n112 ++ n113 ++ n114 ++ n115 ++ n116)) prefixCast
  simpa only [numeric,List.append_assoc] using joined
#print axioms native
end Input
end AspisR1.JFu_Q25Source
