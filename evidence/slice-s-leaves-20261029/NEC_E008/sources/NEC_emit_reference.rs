pub fn emit_ref(validation:bool,encoded:bool,magic:bool)->Result<(),u8>{if !validation || !encoded || !magic{Err(0)}else{Ok(())}}
