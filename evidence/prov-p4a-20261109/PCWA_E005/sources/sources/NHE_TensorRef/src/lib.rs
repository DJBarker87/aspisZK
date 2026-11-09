pub fn tensor_ref(mut output:[[u32;4];64],j:usize,n:usize,products:[[u32;4];4])->[[u32;4];64]{output[j]=products[0];output[j+n]=products[1];output[j+2*n]=products[2];output[j+3*n]=products[3];output}
