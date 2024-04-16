datatype bit = ZEROBIT | ONEBIT
datatype binary = ZERO | TWICE_PLUS of (* binary bit)

val rec int_of_binary = 
    fn n -> match n with 
        | (ZERO) = 0  
        | (TWICE_PLUS {bin (ZEROBIT)}) = (* 2 (int_of_binary bin))  
        | (TWICE_PLUS {bin (ONEBIT)}) = (+ 1 (* 2 (int_of_binary bin)))

val test = fn abc -> match abc with | (ZERO) = 0 | (TWICE_PLUS {(ZERO) bit}) = 5

(int_of_binary (TWICE_PLUS {(TWICE_PLUS {(ZERO) (ONEBIT)}) (ZEROBIT)}))
