

(define has-predecessor-in? (node graph)
  (if (null? graph) #f
      (if (= node (snd (car graph))) #t
          (has-predecessor-in? node (cdr graph)))))

is equivalent to:

val rec has-predecessor-in? = fn node graph -> if (null? graph) false (if (= node (car graph)) true (has-predecessor-in? node (cdr graph)))

fn a -> let val pee = (+ a 3) val hi = (|| false a) in hi

val rec hello = fn n -> (hello n)

(lambda (x a) (let ((y (x a))) y))
fn x a -> let val y = (x a) in y

<function> : (forall [t0, t1] ([([t1] -> t0), t1] -> t0))

<function> : (forall ['a 'b] (('a -> 'b) 'a -> 'b))

(define member? (x ps) 
	(if (null? ps) #f (if (= x (car ps)) #t (member? x (cdr ps)))))

val rec member? = fn x ps -> if (null? ps) false (if (= x (car ps)) true (member? x (cdr ps)))