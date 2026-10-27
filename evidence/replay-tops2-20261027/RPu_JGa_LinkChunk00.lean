import RPu_JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk00
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073472#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 27#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 32#u16, slot := 0#u8, pattern := 0#u8 }
    },
{
      tag := 1124073473#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 43#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 48#u16, slot := 0#u8, pattern := 0#u8 }
    },
{
      tag := 1124073474#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 411#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 416#u16, slot := 0#u8, pattern := 0#u8 }
    },
{
      tag := 1124073475#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 443#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 448#u16, slot := 0#u8, pattern := 0#u8 }
    },
{
      tag := 1124073476#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 459#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 464#u16, slot := 0#u8, pattern := 0#u8 }
    },
{
      tag := 1124073477#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 491#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 496#u16, slot := 0#u8, pattern := 0#u8 }
    },
{
      tag := 1124073478#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 507#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 512#u16, slot := 0#u8, pattern := 0#u8 }
    },
{
      tag := 1124073479#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 11#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 28#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073480#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 12#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 412#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073481#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 44#u16, slot := 0#u8, pattern := 2#u8 },
      consumer := { row := 428#u16, slot := 0#u8, pattern := 3#u8 }
    },
{
      tag := 1124073482#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 60#u16, slot := 0#u8, pattern := 4#u8 },
      consumer := { row := 428#u16, slot := 1#u8, pattern := 5#u8 }
    },
{
      tag := 1124073483#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 44#u16, slot := 1#u8, pattern := 6#u8 },
      consumer := { row := 1008#u16, slot := 0#u8, pattern := 7#u8 }
    },
{
      tag := 1124073484#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 460#u16, slot := 0#u8, pattern := 6#u8 },
      consumer := { row := 1010#u16, slot := 0#u8, pattern := 7#u8 }
    },
{
      tag := 1124073485#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 508#u16, slot := 0#u8, pattern := 6#u8 },
      consumer := { row := 1012#u16, slot := 0#u8, pattern := 7#u8 }
    },
{
      tag := 1124073486#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1008#u16, slot := 0#u8, pattern := 7#u8 },
      consumer := { row := 1014#u16, slot := 0#u8, pattern := 6#u8 }
    },
{
      tag := 1124073487#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1010#u16, slot := 0#u8, pattern := 7#u8 },
      consumer := { row := 1014#u16, slot := 1#u8, pattern := 8#u8 }
    },
{
      tag := 1124073488#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1012#u16, slot := 0#u8, pattern := 7#u8 },
      consumer := { row := 1015#u16, slot := 0#u8, pattern := 8#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,Good,Endpoint]
  repeat' constructor
  all_goals first | scalar_tac | simp
#print axioms all
end AspisR1.JGa_LinkChunk00
