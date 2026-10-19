    fn finish(&self,weights:&mut[K]) {for (i,w) in weights.iter_mut().enumerate(){*w=self.value(i);}}
