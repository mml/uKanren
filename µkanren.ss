(define-syntax (λ stx)
  (syntax-case stx ()
    [(_ args b ...) #'(lambda args b ...)]))
(define (var c) (gensym "var" (string-append "var" (number->string c))))
(define (var? x) (and (gensym? x)
                      (string=? "var" (symbol->string x))))
(define (var=? x1 x2) (eq? x1 x2))

(define (walk u s)
  (let ([pr (and (var? u) (assp (λ (v) (var=? u v)) s))])
    (if pr (walk (cdr pr) s) u)))

(define (ext-s x v s) `((, x . , v) . , s))

(define (≡ u v)
  (λ (s/c)
     (let ([s (unify u v (car s/c))])
       (if s (unit `(, s . , (cdr s/c))) mzero))))
(define == ≡)

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (unify u v s)
  (let ([u (walk u s)] [v (walk v s)])
    (cond
      [(and (var? u) (var? v) (var=? u v)) s]
      [(var? u) (ext-s u v s)]
      [(var? v) (ext-s v u s)]
      [(and (pair? u) (pair? v))
            (let ([s (unify (car u) (car v) s)])
              (and s (unify (cdr u) (cdr v) s)))]
      [else (and (eqv? u v) s)])))

(define (call/fresh f)
  (λ (s/c)
     (let ([c (cdr s/c)])
       ((f (var c)) `(, (car s/c) . , (+ c 1))))))

(define (disj g1 g2) (λ (s/c) (mplus (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (λ (s/c) (bind (g1 s/c) g2)))

(define (mplus $1 $2)
  (cond
    [(null? $1) $2]
    [(procedure? $1) (delay (mplus $2 (force $1)))]
    ;[(procedure? $1) (delay (mplus (force $1) $2))]
    [else (cons (car $1) (mplus (cdr $1) $2))]))

(define (bind $ g)
  (cond
    [(null? $) mzero]
    [(procedure? $) (delay (bind (force $) g))]
    [else (mplus (g (car $)) (bind (cdr $) g))]))

(define (test-fives-and-sixes)
  (define (fives x)
    (disj
      (≡ 5 x)
      (λ (s/c)
        (delay ((fives x) s/c)))))
  (define (sixes x)
    (disj
      (≡ 6 x)
      (λ (s/c)
        (delay ((sixes x) s/c)))))
  (define fives-and-sixes
    (call/fresh
      (λ (x)
        (disj (fives x) (sixes x)))))
  (let ([$ (fives-and-sixes empty-state)])
    (cons (car $) (force (cdr $)))))

(define-syntax Zzz
  (syntax-rules ()
    [(_ g) (λ (s/c) (delay (g s/c)))]))
(define-syntax conj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g0 g ...) (conj (Zzz g0) (conj+ g ...))]))
(define-syntax disj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g0 g ...) (disj (Zzz g0) (disj+ g ...))]))
(define-syntax conde
  (syntax-rules ()
    [(_ (g0 g ...) ...) (disj+ (conj+ g0 g ...) ...)]))
(define-syntax fresh
  (syntax-rules ()
    [(_ () g0 g ...) (conj+ g0 g ...)]
    [(_ (x0 x ...) g0 g ...)
     (call/fresh (λ (x0) (fresh (x ...) g0 g ...)))]))

(define (pull $) (if (procedure? $) (pull (force $)) $))
(define (take-all $)
  (let ([$ (pull $)])
    (if (null? $) '() (cons (car $) (take-all (cdr $))))))
(define (take n $)
  (if (zero? n) '()
    (let ([$ (pull $)])
      (cond
        [(null? $) '()]
        [else (cons (car $) (take (sub1 n) (cdr $)))]))))

(define (mK-reify s/c*)
  (map reify-state/1st-var s/c*))

(define (reify-state/1st-var s/c)
  (let ([v (walk* (var 0) (car s/c))])
    (walk* v (reify-s v '()))))

(define (reify-s v s)
  (let ([v (walk v s)])
    (cond
      [(var? v)
       (let ([n (reify-name (length s))])
         (cons `(,v . ,n) s))]
      [(pair? v) (reify-s (cdr v) (reify-s (car v) s))]
      [else s])))

(define (reify-name n)
  (string->symbol
    (string-append "_" (number->string n))))

(define (walk* v s)
  (let ([v (walk v s)])
    (cond
      [(var? v) v]
      [(pair? v) (cons (walk* (car v) s)
                       (walk* (cdr v) s))]
      [else v])))

(define empty-state `(,mzero . 0))
(define (call/empty-state g) (g empty-state))

(define-syntax run
  (syntax-rules ()
    [(_ n (x ...) g0 g ...)
     (mK-reify (take n (call/empty-state
                         (fresh (x ...) g0 g ... ))))]))
(define-syntax run*
  (syntax-rules ()
    [(_ (x ...) g0 g ...)
     (mK-reify (take-all (call/empty-state
                           (fresh (x ...) g0 g ... ))))]))
