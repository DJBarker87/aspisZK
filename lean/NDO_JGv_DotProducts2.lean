import NDO_JGv_DotData
import SAQ_MixedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotProducts2
open Aeneas Aeneas.Std Result
open JGv_DotData
def product32 : E := ⟨⟨⟨1421711906#u32,57694694#u32⟩,⟨1786593714#u32,1275322213#u32⟩⟩,⟨⟨1388096057#u32,1101574282#u32⟩,⟨422684278#u32,1168616040#u32⟩⟩⟩
theorem mul32 : SAQ_MixedSource.mulE (field ⟨32,by decide⟩) (JGv_WeightsData.cell ⟨32,by decide⟩)=ok product32 := by with_unfolding_all rfl
#print axioms mul32
theorem add32 : FIn_Primitives.add v32 product32=ok v33 := by with_unfolding_all rfl
#print axioms add32
theorem step32 : CheckpointBytes5Output.ofE (state 33)=
    CheckpointBytes5Output.ofE (state 32)+term ⟨32,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical32
    (JGv_WeightsData.canonical ⟨32,by decide⟩) mul32
  exact (FIn_Primitives.add_value _ _ _ add32).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v32+t) product.1)
#print axioms step32
def product33 : E := ⟨⟨⟨889838951#u32,679543003#u32⟩,⟨1501037023#u32,2058212655#u32⟩⟩,⟨⟨995181290#u32,1759177136#u32⟩,⟨1200208366#u32,202318744#u32⟩⟩⟩
theorem mul33 : SAQ_MixedSource.mulE (field ⟨33,by decide⟩) (JGv_WeightsData.cell ⟨33,by decide⟩)=ok product33 := by with_unfolding_all rfl
#print axioms mul33
theorem add33 : FIn_Primitives.add v33 product33=ok v34 := by with_unfolding_all rfl
#print axioms add33
theorem step33 : CheckpointBytes5Output.ofE (state 34)=
    CheckpointBytes5Output.ofE (state 33)+term ⟨33,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical33
    (JGv_WeightsData.canonical ⟨33,by decide⟩) mul33
  exact (FIn_Primitives.add_value _ _ _ add33).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v33+t) product.1)
#print axioms step33
def product34 : E := ⟨⟨⟨1446869930#u32,1853101658#u32⟩,⟨1504149717#u32,1547639542#u32⟩⟩,⟨⟨117888318#u32,512226433#u32⟩,⟨277756472#u32,276872566#u32⟩⟩⟩
theorem mul34 : SAQ_MixedSource.mulE (field ⟨34,by decide⟩) (JGv_WeightsData.cell ⟨34,by decide⟩)=ok product34 := by with_unfolding_all rfl
#print axioms mul34
theorem add34 : FIn_Primitives.add v34 product34=ok v35 := by with_unfolding_all rfl
#print axioms add34
theorem step34 : CheckpointBytes5Output.ofE (state 35)=
    CheckpointBytes5Output.ofE (state 34)+term ⟨34,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical34
    (JGv_WeightsData.canonical ⟨34,by decide⟩) mul34
  exact (FIn_Primitives.add_value _ _ _ add34).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v34+t) product.1)
#print axioms step34
def product35 : E := ⟨⟨⟨1371743187#u32,223483515#u32⟩,⟨298399933#u32,1008295728#u32⟩⟩,⟨⟨1634621141#u32,729480259#u32⟩,⟨2129041275#u32,1852968515#u32⟩⟩⟩
theorem mul35 : SAQ_MixedSource.mulE (field ⟨35,by decide⟩) (JGv_WeightsData.cell ⟨35,by decide⟩)=ok product35 := by with_unfolding_all rfl
#print axioms mul35
theorem add35 : FIn_Primitives.add v35 product35=ok v36 := by with_unfolding_all rfl
#print axioms add35
theorem step35 : CheckpointBytes5Output.ofE (state 36)=
    CheckpointBytes5Output.ofE (state 35)+term ⟨35,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical35
    (JGv_WeightsData.canonical ⟨35,by decide⟩) mul35
  exact (FIn_Primitives.add_value _ _ _ add35).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v35+t) product.1)
#print axioms step35
def product36 : E := ⟨⟨⟨7730248#u32,1000680035#u32⟩,⟨1208536194#u32,636735190#u32⟩⟩,⟨⟨1928913256#u32,180867655#u32⟩,⟨469146759#u32,739719755#u32⟩⟩⟩
theorem mul36 : SAQ_MixedSource.mulE (field ⟨36,by decide⟩) (JGv_WeightsData.cell ⟨36,by decide⟩)=ok product36 := by with_unfolding_all rfl
#print axioms mul36
theorem add36 : FIn_Primitives.add v36 product36=ok v37 := by with_unfolding_all rfl
#print axioms add36
theorem step36 : CheckpointBytes5Output.ofE (state 37)=
    CheckpointBytes5Output.ofE (state 36)+term ⟨36,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical36
    (JGv_WeightsData.canonical ⟨36,by decide⟩) mul36
  exact (FIn_Primitives.add_value _ _ _ add36).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v36+t) product.1)
#print axioms step36
def product37 : E := ⟨⟨⟨887419428#u32,1317190034#u32⟩,⟨1466840793#u32,231040393#u32⟩⟩,⟨⟨2039363538#u32,1619010605#u32⟩,⟨2116642010#u32,2128604257#u32⟩⟩⟩
theorem mul37 : SAQ_MixedSource.mulE (field ⟨37,by decide⟩) (JGv_WeightsData.cell ⟨37,by decide⟩)=ok product37 := by with_unfolding_all rfl
#print axioms mul37
theorem add37 : FIn_Primitives.add v37 product37=ok v38 := by with_unfolding_all rfl
#print axioms add37
theorem step37 : CheckpointBytes5Output.ofE (state 38)=
    CheckpointBytes5Output.ofE (state 37)+term ⟨37,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical37
    (JGv_WeightsData.canonical ⟨37,by decide⟩) mul37
  exact (FIn_Primitives.add_value _ _ _ add37).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v37+t) product.1)
#print axioms step37
def product38 : E := ⟨⟨⟨990993127#u32,1376984919#u32⟩,⟨1193960949#u32,1352322362#u32⟩⟩,⟨⟨427142205#u32,1989553666#u32⟩,⟨526359237#u32,1453615395#u32⟩⟩⟩
theorem mul38 : SAQ_MixedSource.mulE (field ⟨38,by decide⟩) (JGv_WeightsData.cell ⟨38,by decide⟩)=ok product38 := by with_unfolding_all rfl
#print axioms mul38
theorem add38 : FIn_Primitives.add v38 product38=ok v39 := by with_unfolding_all rfl
#print axioms add38
theorem step38 : CheckpointBytes5Output.ofE (state 39)=
    CheckpointBytes5Output.ofE (state 38)+term ⟨38,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical38
    (JGv_WeightsData.canonical ⟨38,by decide⟩) mul38
  exact (FIn_Primitives.add_value _ _ _ add38).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v38+t) product.1)
#print axioms step38
def product39 : E := ⟨⟨⟨88747342#u32,1665398775#u32⟩,⟨1472918116#u32,911563144#u32⟩⟩,⟨⟨1609484196#u32,528589671#u32⟩,⟨1181639348#u32,1332452082#u32⟩⟩⟩
theorem mul39 : SAQ_MixedSource.mulE (field ⟨39,by decide⟩) (JGv_WeightsData.cell ⟨39,by decide⟩)=ok product39 := by with_unfolding_all rfl
#print axioms mul39
theorem add39 : FIn_Primitives.add v39 product39=ok v40 := by with_unfolding_all rfl
#print axioms add39
theorem step39 : CheckpointBytes5Output.ofE (state 40)=
    CheckpointBytes5Output.ofE (state 39)+term ⟨39,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message32.canonical39
    (JGv_WeightsData.canonical ⟨39,by decide⟩) mul39
  exact (FIn_Primitives.add_value _ _ _ add39).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v39+t) product.1)
#print axioms step39
def product40 : E := ⟨⟨⟨638100004#u32,699652417#u32⟩,⟨1919805536#u32,471582423#u32⟩⟩,⟨⟨63362495#u32,941974001#u32⟩,⟨1039363205#u32,278240706#u32⟩⟩⟩
theorem mul40 : SAQ_MixedSource.mulE (field ⟨40,by decide⟩) (JGv_WeightsData.cell ⟨40,by decide⟩)=ok product40 := by with_unfolding_all rfl
#print axioms mul40
theorem add40 : FIn_Primitives.add v40 product40=ok v41 := by with_unfolding_all rfl
#print axioms add40
theorem step40 : CheckpointBytes5Output.ofE (state 41)=
    CheckpointBytes5Output.ofE (state 40)+term ⟨40,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical40
    (JGv_WeightsData.canonical ⟨40,by decide⟩) mul40
  exact (FIn_Primitives.add_value _ _ _ add40).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v40+t) product.1)
#print axioms step40
def product41 : E := ⟨⟨⟨1561418161#u32,170062763#u32⟩,⟨2007994853#u32,902006636#u32⟩⟩,⟨⟨545979420#u32,878583491#u32⟩,⟨2077643735#u32,268185083#u32⟩⟩⟩
theorem mul41 : SAQ_MixedSource.mulE (field ⟨41,by decide⟩) (JGv_WeightsData.cell ⟨41,by decide⟩)=ok product41 := by with_unfolding_all rfl
#print axioms mul41
theorem add41 : FIn_Primitives.add v41 product41=ok v42 := by with_unfolding_all rfl
#print axioms add41
theorem step41 : CheckpointBytes5Output.ofE (state 42)=
    CheckpointBytes5Output.ofE (state 41)+term ⟨41,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical41
    (JGv_WeightsData.canonical ⟨41,by decide⟩) mul41
  exact (FIn_Primitives.add_value _ _ _ add41).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v41+t) product.1)
#print axioms step41
def product42 : E := ⟨⟨⟨40797704#u32,1571940165#u32⟩,⟨1236264807#u32,1917212285#u32⟩⟩,⟨⟨2048470621#u32,1388239525#u32⟩,⟨128528760#u32,1892064332#u32⟩⟩⟩
theorem mul42 : SAQ_MixedSource.mulE (field ⟨42,by decide⟩) (JGv_WeightsData.cell ⟨42,by decide⟩)=ok product42 := by with_unfolding_all rfl
#print axioms mul42
theorem add42 : FIn_Primitives.add v42 product42=ok v43 := by with_unfolding_all rfl
#print axioms add42
theorem step42 : CheckpointBytes5Output.ofE (state 43)=
    CheckpointBytes5Output.ofE (state 42)+term ⟨42,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical42
    (JGv_WeightsData.canonical ⟨42,by decide⟩) mul42
  exact (FIn_Primitives.add_value _ _ _ add42).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v42+t) product.1)
#print axioms step42
def product43 : E := ⟨⟨⟨525566812#u32,40717311#u32⟩,⟨416576315#u32,811344315#u32⟩⟩,⟨⟨257361897#u32,276556868#u32⟩,⟨343318316#u32,1277753693#u32⟩⟩⟩
theorem mul43 : SAQ_MixedSource.mulE (field ⟨43,by decide⟩) (JGv_WeightsData.cell ⟨43,by decide⟩)=ok product43 := by with_unfolding_all rfl
#print axioms mul43
theorem add43 : FIn_Primitives.add v43 product43=ok v44 := by with_unfolding_all rfl
#print axioms add43
theorem step43 : CheckpointBytes5Output.ofE (state 44)=
    CheckpointBytes5Output.ofE (state 43)+term ⟨43,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical43
    (JGv_WeightsData.canonical ⟨43,by decide⟩) mul43
  exact (FIn_Primitives.add_value _ _ _ add43).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v43+t) product.1)
#print axioms step43
def product44 : E := ⟨⟨⟨1421044535#u32,574542119#u32⟩,⟨538049120#u32,1373650005#u32⟩⟩,⟨⟨5253469#u32,510815793#u32⟩,⟨121206599#u32,1494712054#u32⟩⟩⟩
theorem mul44 : SAQ_MixedSource.mulE (field ⟨44,by decide⟩) (JGv_WeightsData.cell ⟨44,by decide⟩)=ok product44 := by with_unfolding_all rfl
#print axioms mul44
theorem add44 : FIn_Primitives.add v44 product44=ok v45 := by with_unfolding_all rfl
#print axioms add44
theorem step44 : CheckpointBytes5Output.ofE (state 45)=
    CheckpointBytes5Output.ofE (state 44)+term ⟨44,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical44
    (JGv_WeightsData.canonical ⟨44,by decide⟩) mul44
  exact (FIn_Primitives.add_value _ _ _ add44).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v44+t) product.1)
#print axioms step44
def product45 : E := ⟨⟨⟨1548106300#u32,812811171#u32⟩,⟨1224056038#u32,80541234#u32⟩⟩,⟨⟨1341701552#u32,1017097897#u32⟩,⟨1744298844#u32,2083406398#u32⟩⟩⟩
theorem mul45 : SAQ_MixedSource.mulE (field ⟨45,by decide⟩) (JGv_WeightsData.cell ⟨45,by decide⟩)=ok product45 := by with_unfolding_all rfl
#print axioms mul45
theorem add45 : FIn_Primitives.add v45 product45=ok v46 := by with_unfolding_all rfl
#print axioms add45
theorem step45 : CheckpointBytes5Output.ofE (state 46)=
    CheckpointBytes5Output.ofE (state 45)+term ⟨45,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical45
    (JGv_WeightsData.canonical ⟨45,by decide⟩) mul45
  exact (FIn_Primitives.add_value _ _ _ add45).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v45+t) product.1)
#print axioms step45
def product46 : E := ⟨⟨⟨1008846630#u32,1782409977#u32⟩,⟨373351015#u32,395425695#u32⟩⟩,⟨⟨1520781341#u32,1552955083#u32⟩,⟨1049846225#u32,803476817#u32⟩⟩⟩
theorem mul46 : SAQ_MixedSource.mulE (field ⟨46,by decide⟩) (JGv_WeightsData.cell ⟨46,by decide⟩)=ok product46 := by with_unfolding_all rfl
#print axioms mul46
theorem add46 : FIn_Primitives.add v46 product46=ok v47 := by with_unfolding_all rfl
#print axioms add46
theorem step46 : CheckpointBytes5Output.ofE (state 47)=
    CheckpointBytes5Output.ofE (state 46)+term ⟨46,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical46
    (JGv_WeightsData.canonical ⟨46,by decide⟩) mul46
  exact (FIn_Primitives.add_value _ _ _ add46).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v46+t) product.1)
#print axioms step46
def product47 : E := ⟨⟨⟨1994063579#u32,1432146103#u32⟩,⟨920864160#u32,222250018#u32⟩⟩,⟨⟨1842697010#u32,1924932648#u32⟩,⟨324096834#u32,759372955#u32⟩⟩⟩
theorem mul47 : SAQ_MixedSource.mulE (field ⟨47,by decide⟩) (JGv_WeightsData.cell ⟨47,by decide⟩)=ok product47 := by with_unfolding_all rfl
#print axioms mul47
theorem add47 : FIn_Primitives.add v47 product47=ok v48 := by with_unfolding_all rfl
#print axioms add47
theorem step47 : CheckpointBytes5Output.ofE (state 48)=
    CheckpointBytes5Output.ofE (state 47)+term ⟨47,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message40.canonical47
    (JGv_WeightsData.canonical ⟨47,by decide⟩) mul47
  exact (FIn_Primitives.add_value _ _ _ add47).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v47+t) product.1)
#print axioms step47
end AspisR1.JGv_DotProducts2
end
