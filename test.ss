(load "µkanren.ss")

;;; This file is merely a running set of test cases where I work out
;;; what the current implementation can and can't do.  This should guide
;;; me as I modify the kanren-du-jour to something more powerful.
;;; Enlightening me in the process!

(define (nullo l)
  (== l '()))

(define (conso a d p)
  (== p `(,a . ,d)))

(define (caro p a)
  (fresh (d)
    (conso a d p)))

(define (cdro p d)
  (fresh (a)
    (conso a d p)))

(define (listo l)
  (conde
    [(nullo l)]
    [(fresh (d)
       (cdro l d)
       (listo d))]))

(define (lolo l)
  (conde
    [(nullo l)]
    [(fresh (a d)
       (conso a d l)
       (listo a)
       (lolo d))]))

(define (singletono l)
  (fresh (d)
    (cdro l d)
    (nullo d)))

(define (loso l)
  (conde
    [(nullo l)]
    [(fresh ( a d)
       (conso a d l)
       (singletono a)
       (loso d))]))

(define (appendo l1 l2 out)
  (conde
    [(nullo l1) (== l2 out)]
    [(fresh (a d rest)
       (conso a d l1)
       (appendo d l2 rest)
       (conso a rest out))]))

(define (membero x l)
  (conde
    [(fresh (a)
       (caro l a)
       (== a x))]
    [(fresh (d)
       (cdro l d)
       (membero x d))]))

(module ((trun* with-printed-goals)
         (trun with-printed-goals))
  (define-syntax (with-printed-goals stx)
    (syntax-case stx ()
      [(_ (g ...) expr ...)
       #'(begin
           (begin (printf "-> ~a\n" 'g) ...)
           expr ...)]))
  (define-syntax (trun* stx)
    (syntax-case stx ()
      [(trun* q g0 g ...)
       #'(with-printed-goals (g0 g ...)
           (prun* q g0 g ...))]
      [(trun* (x ...) g0 g ...)
       #'(with-printed-goals (g0 g ...)
           (prun* (x ...) g0 g ...))]))
  (define-syntax (trun stx)
    (syntax-case stx ()
      [(trun n q g0 g ...)
       #'(with-printed-goals (g0 g ...)
           (prun n q g0 g ...))])))

(trun* q (nullo '()))
(trun* q (nullo '(a)))
(trun* l (conso 'the '(quick brown fox) l))
(trun* a (caro '(the quick brown fox) a))
(trun* d (cdro '(the quick brown fox) d))
(trun* q (listo '()))
(trun* q (listo '(foo)))
(trun* q (listo #t))
(trun* q (singletono '(x)))
(trun* q (singletono '()))
(trun* q (loso '()))
(trun* q (loso '((x) (y))))
(trun* q (loso '(() ())))
(trun* q (lolo '()))
(trun* q (lolo '(() () ())))
(trun* q (lolo '(a b c)))
(trun* q (listo '(foo bar baz quux)))
(trun* l (appendo '(the quick brown fox)
                  '(jumped over the lazy dog)
                  l))
#;(trun* l1 (appendo l1                     ; Currently does not terminate
                   '(and eggs)
                   '(hot tea and eggs)))
(trun* l2 (appendo '(hot tea)
                   l2
                   '(hot tea and eggs)))
(trun* q (membero 'x '(x)))
(trun* q (membero 'x '(x y)))
(trun* q (membero 'x '(y x)))
(trun* q (membero 'x '()))
(trun* q (membero 'x '(foo bar)))
(trun* x (membero x '(foo bar)))
(trun* y (membero 'foo `(,y bar)))
(trun* y (membero y '()))
(trun* y (membero y '(foo bar baz)))
(trun* y (membero 'foo `(foo ,y baz)))
(trun* (x y) (membero x `(foo ,y baz)))
(trun 5 l (membero 'tofu l))
