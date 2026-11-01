//! Token-exact proof-only copy of the native serializer and projection.
use aspis_core::{field::M31,state_only_prefix::r0::Error};
use aspis_statement::{poseidon2::Digest,pool_v1::{
 payment_relation::{PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1},
 pair_tree_profile::PoolV1PairLatePublicStatementV1}};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompiledVariant {
    PrivateTransfer,
    Withdrawal,
}
#[derive(Clone, Copy)]
struct SemanticPublic<'a> {
    variant: CompiledVariant,
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient: Option<Digest>,
    change: Digest,
    withdrawal_amount: Option<u32>,
    transition: &'a PoolV1PairLatePublicStatementV1,
}
fn private_public<'a>(
    public: &PoolV1PrivateTransferPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::PrivateTransfer,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: Some(public.recipient_commitment),
        change: public.change_commitment,
        withdrawal_amount: None,
        transition,
    }
}
fn withdrawal_public<'a>(
    public: &PoolV1WithdrawalPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::Withdrawal,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: None,
        change: public.change_commitment,
        withdrawal_amount: Some(public.amount),
        transition,
    }
}
#[derive(Clone, Copy)]
pub enum Public<'a> {
        Transfer(
            &'a PoolV1PrivateTransferPublicV1,
            &'a PoolV1PairLatePublicStatementV1,
        ),
        Withdrawal(
            &'a PoolV1WithdrawalPublicV1,
            &'a PoolV1PairLatePublicStatementV1,
        ),
    }
impl<'a> Public<'a> {
fn semantic(self) -> SemanticPublic<'a> {
            match self {
                Self::Transfer(public, transition) => private_public(public, transition),
                Self::Withdrawal(public, transition) => withdrawal_public(public, transition),
            }
        }
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
            // The fixed width is checked at both call sites. Explicit calls
            // avoid nested frontier loops during source extraction.
            fn frontier(out: &mut Vec<u8>, values: &[Digest; 20]) -> Result<(), Error> {
                fields(out, &values[0])?;
                fields(out, &values[1])?;
                fields(out, &values[2])?;
                fields(out, &values[3])?;
                fields(out, &values[4])?;
                fields(out, &values[5])?;
                fields(out, &values[6])?;
                fields(out, &values[7])?;
                fields(out, &values[8])?;
                fields(out, &values[9])?;
                fields(out, &values[10])?;
                fields(out, &values[11])?;
                fields(out, &values[12])?;
                fields(out, &values[13])?;
                fields(out, &values[14])?;
                fields(out, &values[15])?;
                fields(out, &values[16])?;
                fields(out, &values[17])?;
                fields(out, &values[18])?;
                fields(out, &values[19])?;
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
            frontier(&mut out, &source.frontier)?;
            fields(&mut out, &after.next_root)?;
            frontier(&mut out, &after.next_frontier)?;
            Ok(out)
        }
}
