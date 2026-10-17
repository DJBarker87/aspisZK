    fn c2(&mut self,columns:[&[K;1024];2])->Result<[u8;32],SError>{
        for (i,c) in columns.into_iter().enumerate(){self.messages[26+i]=c.map(E::from_qm31);}
        let c=if let Some(salts)=self.c2_salts.take(){Commitment::new_salted(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant,salts)}else{Commitment::new(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant)}.map_err(|_|SError::Public)?;
        let root=c.root();self.c2=Some(c);Ok(root)
    }