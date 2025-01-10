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

(define (appendo l1 l2 out)
  (conde
    [(nullo l1) (== l2 out)]
    [(fresh (a d rest)
       (conso a d l1)
       (appendo d l2 rest)
       (conso a rest out))]))

(prun* q (nullo '()))
(prun* q (nullo '(a)))
(prun* l (conso 'the '(quick brown fox) l))
(prun* a (caro '(the quick brown fox) a))
(prun* d (cdro '(the quick brown fox) d))
(prun* l (appendo '(the quick brown fox)
                  '(jumped over the lazy dog)
                  l))
#;(prun* l1 (appendo l1                     ; Currently does not terminate
                   '(and eggs)
                   '(hot tea and eggs)))
(prun* l2 (appendo '(hot tea)
                   l2
                   '(hot tea and eggs)))
