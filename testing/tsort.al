

(define has-predecessor-in? (node graph)
  (if (null? graph) #f
      (if (= node (snd (car graph))) #t
          (has-predecessor-in? node (cdr graph)))))

is equivalent to:

val rec has-predecessor-in? = fn node graph -> if (null? graph) false (if (= node (car graph)) true (has-predecessor-in? node (cdr graph)))

fn a -> let val pee = (+ a 3) val hi = (|| false a) in hi