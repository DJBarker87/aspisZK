import R1Z.PV_B2_RawWeights253Funs
open Aeneas Aeneas.Std Result
#print Aeneas.Std.Error
#print Aeneas.Std.massert
#print Aeneas.Std.Array.index_usize
#eval match PV_B2_253b10.host_weights.host_row .D 1024#usize with
  | .ok _ => "success"
  | .fail e => reprStr e
  | .div => "divergence"
#eval match Array.index_usize (Array.repeat 1024#usize 0#u16) 1024#usize with
  | .ok _ => "success"
  | .fail e => reprStr e
  | .div => "divergence"
