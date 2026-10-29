//! Concrete retained-key policy, not a restriction on the adapter's public policy.
use crate::diagnostics::{anyhow, ensure, Result, err};
use serde_json::{json, Value};
use solana_program::pubkey::Pubkey;
use std::str::FromStr;

pub const CAP: usize = 8;
pub struct Accounts {
    keys: [Pubkey; CAP],
    entered: usize,
}
impl Accounts {
    pub fn parse(q: &Value) -> Result<Self> {
        ensure!(q.get("proof_account").is_none(), "legacy proof_account input is unsupported");
        let list = q["proof_accounts"].as_array().ok_or_else(|| anyhow!("proof_accounts must be eight public keys"))?;
        ensure!(list.len() == CAP, "proof_accounts must contain eight public keys");
        let mut keys = [Pubkey::default(); CAP];
        for (i, value) in list.iter().enumerate() {
            let text = value.as_str().ok_or_else(|| anyhow!("proof account must be a string"))?;
            let key = Pubkey::from_str(text).map_err(err)?;
            ensure!(key.to_string() == text && key != Pubkey::default(), "noncanonical/zero proof account");
            ensure!(!keys[..i].contains(&key), "duplicate proof account");
            keys[i] = key;
        }
        Ok(Self { keys, entered: 0 })
    }
    pub fn nonce(&mut self, k: usize) -> [u8; 32] {
        // The unchanged adapter enters precisely 0..ATTEMPT_CAP in order.
        assert_eq!(k, self.entered, "selected adapter callback order changed");
        let nonce = self.keys[k].to_bytes();
        self.entered += 1;
        nonce
    }
    /// Add the successful key to the actual settlement list and build stage1
    /// roles together, so publication cannot independently choose another key.
    pub fn publication(&self, attempts: usize, settlement: &mut Vec<Value>,
                       public: Pubkey, checkpoint: Pubkey) -> Result<Value> {
        ensure!(settlement.len() == 10, "unexpected settlement proof-account position");
        let (_, key) = self.selected(attempts)?;
        let proof = json!([key.to_string(), false, false]);
        settlement.push(proof.clone());
        Ok(json!([proof, [public.to_string(), false, false],
                  [checkpoint.to_string(), false, true]]))
    }
    pub fn selected(&self, attempts: usize) -> Result<(usize, Pubkey)> {
        ensure!((1..=CAP).contains(&attempts) && attempts == self.entered, "invalid successful attempt count");
        Ok((attempts - 1, self.keys[attempts - 1]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn request() -> Value { json!({"proof_accounts": (1..=8).map(|i| Pubkey::new_from_array([i;32]).to_string()).collect::<Vec<_>>()}) }
    #[test]
    fn first_rejected_and_last_selection() {
        for attempts in [1, 2, 8] {
            let q = request(); let mut policy = Accounts::parse(&q).unwrap();
            for k in 0..attempts { assert_eq!(policy.nonce(k), [k as u8 + 1;32]); }
            let (index, key) = policy.selected(attempts).unwrap();
            assert_eq!(index, attempts - 1); assert_eq!(key.to_string(), q["proof_accounts"][index]);
            let mut settlement = vec![Value::Null; 10];
            let public = Pubkey::new_from_array([20; 32]);
            let checkpoint = Pubkey::new_from_array([21; 32]);
            let stage1 = policy.publication(attempts, &mut settlement, public, checkpoint).unwrap();
            assert_eq!(settlement[10], json!([key.to_string(), false, false]));
            assert_eq!(stage1[0], settlement[10]);
            assert_eq!(stage1[1], json!([public.to_string(), false, false]));
            assert_eq!(stage1[2], json!([checkpoint.to_string(), false, true]));
            assert!(policy.publication(attempts, &mut settlement, public, checkpoint).is_err());
            assert!(policy.selected(0).is_err()); assert!(policy.selected(9).is_err());
        }
    }
    #[test]
    fn invalid_abi() {
        for q in [json!({}), json!({"proof_accounts": []}), json!({"proof_accounts": vec!["bad"; 8]})] {
            assert!(Accounts::parse(&q).is_err());
        }
        let mut q = request(); q["proof_accounts"][7] = q["proof_accounts"][0].clone();
        assert!(Accounts::parse(&q).is_err());
        let mut q = request(); q["proof_accounts"][0] = json!(Pubkey::default().to_string());
        assert!(Accounts::parse(&q).is_err());
    }
}

#[cfg(test)]
mod route_tests {
    #[test]
    fn shipped_runner_has_no_generic96_fallback() {
        let planner = include_str!("plan.rs");
        let runner = include_str!("../devnet_spend.rs");
        assert_eq!(planner.matches("RealR1_client::prove_for_proof_accounts(").count(), 1);
        for source in [planner, runner] {
            for forbidden in ["prove_masked_retrying(", "prove_masked_retrying_with(",
                              "prove_masked_attempt(", "StateOnlyAttemptSecrets", " prover::", "{prover,"] {
                assert!(!source.contains(forbidden), "alternative prover route: {forbidden}");
            }
        }
        assert!(runner.contains("plan::run(&q)?"));
    }
}
