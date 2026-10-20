            let mut partials=[E::ZERO;4];
            for s in 0..4 {
                let mut dot=crate::fast_pairing::EbyKDot::new();
                for j in 0..16 {
                    dot.push(field(f,16*s+j),common[j]).map_err(|_|Error::Parse)?;
                }
                partials[s]=dot.finish();
            }
