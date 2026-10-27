import RPv_JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk05
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073557#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 171#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 941#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073558#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 942#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 188#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073559#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 942#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 176#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073560#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 187#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 945#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073561#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 946#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 204#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073562#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 946#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 192#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073563#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 203#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 949#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073564#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 950#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 220#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073565#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 950#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 208#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073566#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 219#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 953#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073567#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 954#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 236#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073568#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 954#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 224#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073569#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 235#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 957#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073570#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 958#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 252#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073571#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 958#u16, slot := 1#u8, pattern := 13#u8 },
      consumer := { row := 240#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073572#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 251#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 961#u16, slot := 0#u8, pattern := 12#u8 }
    },
{
      tag := 1124073573#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 962#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 268#u16, slot := 0#u8, pattern := 1#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,Good,Endpoint]
  repeat' constructor
  all_goals first | scalar_tac | simp
#print axioms all
end AspisR1.JGa_LinkChunk05
