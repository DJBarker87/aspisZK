pub type Key=[u8;32];
#[derive(Clone,Copy)]
pub struct Account {pub key:Key,pub owner:Key,pub signer:bool,pub writable:bool,pub executable:bool}
#[derive(Clone,Copy,PartialEq,Eq)]
pub enum Error {InvalidVerifierProgram,NotEnoughAccountKeys,InvalidVerifierProof,InvalidPayer,InvalidSystemProgram,InvalidTokenProgram,InvalidArgument}
pub fn supported_loader(owner:&Key,loaders:&[Key;3])->bool {owner==&loaders[0]||owner==&loaders[1]||owner==&loaders[2]}
pub fn verifier(account:&Account,selected:&Key,loaders:&[Key;3])->Result<(),Error>{
if account.key!=*selected||!account.executable||account.signer||account.writable||!supported_loader(&account.owner,loaders){return Err(Error::InvalidVerifierProgram);}Ok(())}
pub fn transport(program:&Account,proof:&Account,checkpoint:Option<&Account>)->Result<Key,Error>{let checkpoint=checkpoint.ok_or(Error::NotEnoughAccountKeys)?;
if proof.key==program.key||proof.executable||proof.signer||proof.writable||checkpoint.owner!=program.key||checkpoint.executable||checkpoint.signer||checkpoint.writable||checkpoint.key==proof.key||checkpoint.key==program.key{return Err(Error::InvalidVerifierProof);}Ok(program.key)}
pub fn payer(payer:&Account,system:&Account,system_id:&Key,native_id:&Key)->Result<(),Error>{
if !payer.signer||!payer.writable||payer.executable||payer.owner!=*system_id{return Err(Error::InvalidPayer);}
if system.key!=*system_id||system.owner!=*native_id||!system.executable||system.signer||system.writable{return Err(Error::InvalidSystemProgram);}Ok(())}
pub fn token(account:&Account,token_id:&Key,loaders:&[Key;3])->Result<(),Error>{if account.key!=*token_id||!account.executable||account.signer||account.writable||!supported_loader(&account.owner,loaders){return Err(Error::InvalidTokenProgram);}Ok(())}
pub fn count(actual:usize,expected:usize)->Result<(),Error>{if actual!=expected{return Err(if actual<expected{Error::NotEnoughAccountKeys}else{Error::InvalidArgument});}Ok(())}
