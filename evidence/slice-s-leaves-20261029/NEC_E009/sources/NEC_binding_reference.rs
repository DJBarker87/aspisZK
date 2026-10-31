pub fn binding_ref<E>(first:Result<(),E>,second:Result<(),E>,mismatch:bool,error:E)->Result<(),E>{first?;second?;if mismatch{Err(error)}else{Ok(())}}
