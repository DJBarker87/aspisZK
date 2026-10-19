        /// SPEC §9 declaration order. Pool/domain/sequence and source current
        /// root are not fields of R0P.Public and are not silently hashed here.
        /// Existing reject-only public guards remain in the terminal.
        pub fn public_bytes(self) -> Result<Vec<u8>, Error> {
            fn fields(out: &mut Vec<u8>, values: &[M31]) -> Result<(), Error> {
                for value in values {
                    if value.0 >= aspis_core::field::P {
                        return Err(Error::Public);
                    }
                    out.extend_from_slice(&value.0.to_le_bytes());
                }
                Ok(())
            }
            let p = self.semantic();
            let mut out = Vec::new();
            out.push(match p.variant {
                CompiledVariant::PrivateTransfer => 0,
                CompiledVariant::Withdrawal => 1,
            });
            fields(&mut out, &p.anchor)?;
            fields(&mut out, &p.nullifier)?;
            fields(&mut out, &[p.asset_id])?;
            out.push(u8::from(p.recipient.is_some()));
            if let Some(value) = p.recipient {
                fields(&mut out, &value)?;
            }
            fields(&mut out, &p.change)?;
            out.push(u8::from(p.withdrawal_amount.is_some()));
            if let Some(value) = p.withdrawal_amount {
                fields(&mut out, &[M31(value)])?;
            }
            let source = p.transition.live_snapshot;
            let after = p.transition.candidate_afterstate;
            out.extend_from_slice(&source.next_pair_index.to_le_bytes());
            for digest in &source.frontier {
                fields(&mut out, digest)?;
            }
            fields(&mut out, &after.next_root)?;
            for digest in &after.next_frontier {
                fields(&mut out, digest)?;
            }
            Ok(out)
        }