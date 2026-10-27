import RPu_JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk03
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073523#u32,
      weight_kind := 4#u8,
      weight_level := 13#u8,
      producer := { row := 747#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 752#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073524#u32,
      weight_kind := 3#u8,
      weight_level := 14#u8,
      producer := { row := 763#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 780#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073525#u32,
      weight_kind := 4#u8,
      weight_level := 14#u8,
      producer := { row := 763#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 768#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073526#u32,
      weight_kind := 3#u8,
      weight_level := 15#u8,
      producer := { row := 779#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 796#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073527#u32,
      weight_kind := 4#u8,
      weight_level := 15#u8,
      producer := { row := 779#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 784#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073528#u32,
      weight_kind := 3#u8,
      weight_level := 16#u8,
      producer := { row := 795#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 812#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073529#u32,
      weight_kind := 4#u8,
      weight_level := 16#u8,
      producer := { row := 795#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 800#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073530#u32,
      weight_kind := 3#u8,
      weight_level := 17#u8,
      producer := { row := 811#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 828#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073531#u32,
      weight_kind := 4#u8,
      weight_level := 17#u8,
      producer := { row := 811#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 816#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073532#u32,
      weight_kind := 3#u8,
      weight_level := 18#u8,
      producer := { row := 827#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 844#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073533#u32,
      weight_kind := 4#u8,
      weight_level := 18#u8,
      producer := { row := 827#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 832#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073534#u32,
      weight_kind := 3#u8,
      weight_level := 19#u8,
      producer := { row := 843#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 860#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073535#u32,
      weight_kind := 4#u8,
      weight_level := 19#u8,
      producer := { row := 843#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 848#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073536#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 59#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 913#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073537#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 914#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 76#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073538#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 914#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 64#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073539#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 75#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 917#u16, slot := 0#u8, pattern := 12#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,Good,Endpoint]
  repeat' constructor
  all_goals first | scalar_tac | simp
#print axioms all
end AspisR1.JGa_LinkChunk03
