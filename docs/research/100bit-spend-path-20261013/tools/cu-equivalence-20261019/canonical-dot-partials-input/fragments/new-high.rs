                let mut high=crate::fast_pairing::EbyKDot::new();
                for s in 0..4 {
                    high.push(partials[s],self.factors[k][4][s]).map_err(|_|Error::Parse)?;
                }
