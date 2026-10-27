import RPv_JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk06
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073574#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 962#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 256#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073575#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 267#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 965#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073576#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 966#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 284#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073577#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 966#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 272#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073578#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 283#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 969#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073579#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 970#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 300#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073580#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 970#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 288#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073581#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 299#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 973#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073582#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 974#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 316#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073583#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 974#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 304#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073584#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 315#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 977#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073585#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 978#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 332#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073586#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 978#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 320#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073587#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 331#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 981#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073588#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 982#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 348#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073589#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 982#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 336#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073590#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 347#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 985#u16, slot := 0#u8, pattern := 12#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,Good,Endpoint]
  repeat' constructor
  all_goals first | scalar_tac | simp
#print axioms all
end AspisR1.JGa_LinkChunk06
