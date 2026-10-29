import NEA_Reference.Funs
import R17CurrentM31Semantics
set_option pp.explicit true in
#print NEA_Reference.line_double_sub_ref
set_option pp.explicit true in
#check fun d : Aeneas.Std.U32 => (d - 1#u32 : Aeneas.Result Aeneas.Std.U32)
#print Aeneas.Std.UScalar.sub
#print Aeneas.Std.U32.wrapping_sub
