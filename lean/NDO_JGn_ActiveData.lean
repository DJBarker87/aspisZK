import NDO_JGn_CopyData
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_ActiveData
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeValue (decode)
def a00 : field.QM31 := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def a08 : field.QM31 := ⟨⟨946370432#u32,97302049#u32⟩,⟨263915033#u32,1384801604#u32⟩⟩
def a16 : field.QM31 := ⟨⟨1744144902#u32,535863875#u32⟩,⟨924139217#u32,1606419470#u32⟩⟩
def a24 : field.QM31 := ⟨⟨742393060#u32,977642027#u32⟩,⟨1736912547#u32,1256794043#u32⟩⟩
def a32 : field.QM31 := ⟨⟨1761888499#u32,654911134#u32⟩,⟨731519042#u32,704053604#u32⟩⟩
def a40 : field.QM31 := ⟨⟨1265259893#u32,1500408477#u32⟩,⟨74972320#u32,1379721892#u32⟩⟩
def a48 : field.QM31 := ⟨⟨825626110#u32,558225935#u32⟩,⟨483074980#u32,1961069927#u32⟩⟩
def a56 : field.QM31 := ⟨⟨1624051465#u32,169699672#u32⟩,⟨2035936820#u32,390853182#u32⟩⟩
def a64 : field.QM31 := ⟨⟨766140686#u32,1850622266#u32⟩,⟨1931269867#u32,1348309306#u32⟩⟩
def block0 : List (Fin 64) := (FJk_ActiveValue.indices.drop 0).take 8
def block1 : List (Fin 64) := (FJk_ActiveValue.indices.drop 8).take 8
def block2 : List (Fin 64) := (FJk_ActiveValue.indices.drop 16).take 8
def block3 : List (Fin 64) := (FJk_ActiveValue.indices.drop 24).take 8
def block4 : List (Fin 64) := (FJk_ActiveValue.indices.drop 32).take 8
def block5 : List (Fin 64) := (FJk_ActiveValue.indices.drop 40).take 8
def block6 : List (Fin 64) := (FJk_ActiveValue.indices.drop 48).take 8
def block7 : List (Fin 64) := (FJk_ActiveValue.indices.drop 56).take 8
end AspisR1.JGn_ActiveData
end
