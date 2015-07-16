#lang racket
(provide (all-defined-out))
;; If you haven't download & install Racket
;; http://racket-lang.org/

;; State :: Store X Counter
;; Goal :: State -> Stream

(define ((ccons x) y) (cons x y))

(define empty-store
  (make-immutable-hasheqv
    '((== . ())
      (=/= . ())
      (not-pairo . ())
      (symbolo . ())
      (absento . ()))))

(define ((== u v) s/c)
  (let ((s (hash-update (car s/c) '== (ccons `(,u . ,v)))))
    (return `(,s . ,(cdr s/c)))))

(define ((=/= u v) s/c)
  (let ((s (hash-update (car s/c) '=/= (ccons `(,u . ,v)))))
    (return `(,s . ,(cdr s/c)))))

(define ((absento u v) s/c)
  (let ((s (hash-update (car s/c) 'absento (ccons `(,u . ,v)))))
    (return `(,s . ,(cdr s/c)))))

(define ((not-pairo u) s/c)
  (let ((s (hash-update (car s/c) 'not-pairo (ccons u))))
    (return `(,s . ,(cdr s/c)))))

(define ((symbolo u) s/c)
  (let ((s (hash-update (car s/c) 'symbolo (ccons u))))
    (return `(,s . ,(cdr s/c)))))

(define (return s/c)
  (if (bad? (car s/c)) '() (list s/c)))

(define (bad? st)
  (let ((== (hash-ref st '==)))
    (cond
      ((good-s? ==) 
       => (lambda (s) 
            (or ((bad-d? (hash-ref st '=/=)) s)
                ((bad-np? (hash-ref st 'not-pairo)) s)
                ((bad-sym? (hash-ref st 'symbolo)) s)
                ((bad-abs? (hash-ref st 'absento)) s))))
      (else #t))))

(define ((bad-np? np-store) s)
  (ormap
   (lambda (t)
     (pair? (find t s)))
   np-store))

(define ((bad-sym? sym-store) s)
  (ormap
   (lambda (t)
     (let ((t (find t s)))
       (and (not (symbol? t))
            (not (var? t)))))
   sym-store))

(define ((bad-d? d-store) s)
  (ormap
   (lambda (pr)
     (equal? (unify (car pr) (cdr pr) s) s))
   d-store))

(define ((bad-abs? abs-store) s)
  (ormap
   (lambda (pr)
     (mem? (car pr) (cdr pr) s))
   abs-store))

(define (mem? u v s)
  (let ((v (find v s)))
    (or (equal? (unify u v s) s)
        (and (pair? v)
             (or (mem? u (car v) s)
                 (mem? u (cdr v) s))))))

;; Subst :: [(Var X Term)]

;; [(Term X Term)] -> Maybe Subst
(define (good-s? s)
  (foldr
   (lambda (pr s)
     (and s (unify (car pr) (cdr pr) s)))
   '()
   s))

;; Term ::= Var | Symbol | Boolean | () | (Term . Term)

(define (find u s)
  (let ((pr (assv u s)))
    (if pr (find (cdr pr) s) u)))

(define (unify u v s)
  (let ((u (find u s)) (v (find v s)))
    (cond
      ((eqv? u v) s)
      ((var? u) `((,u . ,v) . ,s))
      ((var? v) `((,v . ,u) . ,s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else #f))))

;; We don't really care what the second argument is**

(define (var n) n)
(define (var? n) (number? n))

;; "an f" (lambda (x) (== x 'cat))
;; call/fresh :: (Var -> Goal) -> Goal
(define ((call/fresh f) s/c)
  (let ((s (car s/c)) (c (cdr s/c)))
    ((f (var c)) `(,s . ,(+ c 1)))))

;; (== 'cat 'cat)
;; (== 'dog 'dog)
;; (== 'horse 'fish)
;; '((horse . fish) (dog . dog) (cat . cat))
;;** Caveat:
;; We should add the "occur? check", to retain soundness.

;; printing convention
(current-print pretty-write)

(define ((disj g1 g2) s/c) ($append (g1 s/c) (g2 s/c)))

(define ($append $1 $2)
  (cond
    ((null? $1) $2)
    ((promise? $1) (delay/name ($append $2 (force $1))))
    (else (cons (car $1) ($append (cdr $1) $2)))))

(define ((conj g1 g2) s/c) ($append-map g2 (g1 s/c)))

(define ($append-map g $)
  (cond
    ((null? $) '())
    ((promise? $) (delay/name ($append-map g (force $))))
    (else ($append (g (car $)) ($append-map g (cdr $))))))

(define-syntax-rule (define-relation (defname . args) g)
  (define ((defname . args) s/c) (delay/name (g s/c))))

;; Stream :: Mature | Immature
;; Mature :: () | State X Stream
;; Immature :: Unit -> Stream

(define (pull $) (if (promise? $) (pull (force $)) $))

(define (take n $)
  (cond
    ((null? $) '())
    ((and n (zero? (- n 1))) (list (car $)))
    (else (cons (car $) 
            (take (and n (- n 1)) (pull (cdr $)))))))

(define (call/initial-state n g)
  (take n (pull (g `(,empty-store . 0)))))

(define-relation (rembero x ls o)
  (disj
    (conj 
      (== ls '())
      (== ls o))
    (call/fresh
      (lambda (a)
        (call/fresh
          (lambda (d)
            (conj
              (== `(,a . ,d) ls)
              (disj
                (conj 
                  (=/= a x) 
                  (call/fresh
                   (lambda (res)
                     (== `(,a . ,res) o)
                     (rembero x d res))))
                (conj 
                  (== a x)
                  (rembero x d o))))))))))

;; github.com/jasonhemann
;; @jhemann @dfried00
