datatype bit = ZEROBIT | ONEBIT
datatype binary = ZERO | TWICE_PLUS of (* bit binary)

val rec int_of_binary = 
    fn n -> match n with 
        | (ZERO) = 0  
        | (TWICE_PLUS {bin (ZEROBIT)}) = (* 2 (int_of_binary bin))  
        | (TWICE_PLUS {bin (ONEBIT)}) = (+ 1 (* 2 (int_of_binary bin)))

(int_of_binary (TWICE_PLUS {(TWICE_PLUS {(ZERO) (ONEBIT)}) (ZEROBIT)}))
