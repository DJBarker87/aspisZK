import JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk07
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073591#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 986#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 364#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073592#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 986#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 352#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073593#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 363#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 989#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073594#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 990#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 380#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073595#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 990#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 368#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073596#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 379#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 993#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073597#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 994#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 396#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073598#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 994#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 384#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073599#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 395#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 997#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073600#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 998#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 876#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073601#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 998#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 864#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073602#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 875#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 1001#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073603#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1002#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 892#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073604#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1002#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 880#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073605#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 891#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 1005#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073606#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1006#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 908#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073607#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1006#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 896#u16, slot := 0#u8, pattern := 10#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,Good,Endpoint]
  repeat' constructor
  all_goals first | scalar_tac | simp
#print axioms all
end AspisR1.JGa_LinkChunk07
