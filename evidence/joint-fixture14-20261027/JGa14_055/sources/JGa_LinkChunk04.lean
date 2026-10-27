import JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk04
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073540#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 918#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 92#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073541#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 918#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 80#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073542#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 91#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 921#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073543#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 922#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 108#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073544#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 922#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 96#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073545#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 107#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 925#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073546#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 926#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 124#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073547#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 926#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 112#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073548#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 123#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 929#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073549#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 930#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 140#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073550#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 930#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 128#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073551#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 139#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 933#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073552#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 934#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 156#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073553#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 934#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 144#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073554#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 155#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 937#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073555#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 938#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 172#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073556#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 938#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 160#u16, slot := 0#u8, pattern := 10#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,List.forall_mem_nil,Good,Endpoint,and_true]
  all_goals scalar_tac
#print axioms all
end AspisR1.JGa_LinkChunk04
