//! Concrete retained-key policy, not a restriction on the adapter's public policy.
use crate::diagnostics::{anyhow, ensure, Result, err};
use serde_json::Value;
use solana_program::pubkey::Pubkey;
use std::str::FromStr;

pub const CAP: usize = 8;
pub struct Accounts {
    keys: [Pubkey; CAP],
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
        Ok(Self { keys })
    }
    pub fn nonce(&self, k: usize) -> [u8; 32] {
        self.keys[k].to_bytes()
    }
    /// Add the successful key to the actual settlement list and build stage1
    /// roles together, so publication cannot independently choose another key.
    pub fn publication(&self, attempts: usize, settlement: &mut Vec<Value>,
                       public: Pubkey, checkpoint: Pubkey) -> Result<Value> {
        ensure!(settlement.len() == 10, "unexpected settlement proof-account position");
        let (_, key) = self.selected(attempts)?;
        let proof = Value::Array(vec![Value::String(key.to_string()),Value::Bool(false),Value::Bool(false)]);
        settlement.push(proof.clone());
        Ok(Value::Array(vec![proof,Value::Array(vec![Value::String(public.to_string()),Value::Bool(false),Value::Bool(false)]),Value::Array(vec![Value::String(checkpoint.to_string()),Value::Bool(false),Value::Bool(true)])]))
    }
    pub fn selected(&self, attempts: usize) -> Result<(usize, Pubkey)> {
        ensure!((1..=CAP).contains(&attempts), "invalid successful attempt count");
        Ok((attempts - 1, self.keys[attempts - 1]))
    }
}

