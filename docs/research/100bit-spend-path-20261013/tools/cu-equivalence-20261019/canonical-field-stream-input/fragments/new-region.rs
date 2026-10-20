                let mut pair=crate::fast_pairing::EbyKDot::new();
                for j in 0..n {pair.push(field(f,j),scratch[j]).map_err(|_|Error::Parse)?;}
