    let mut dot=crate::fast_pairing::EbyKDot::new();
    for (j,w) in a.weights.iter().enumerate() {dot.push(field(v.final_message,j),*w).map_err(|_|Error::Parse)?;}
