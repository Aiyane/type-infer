(define-syntax λ
  (syntax-rules ()
    [(_ arg* bd bd* ...)
      (lambda arg* bd bd* ...)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; var ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define var
  (λ (x)
    (vector x)))
(define var?
  (λ (v)
    (vector? v)))
(define var=?
  (λ (v₁ v₂)
    (eq? (vector-ref v₁ 0) (vector-ref v₂ 0))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; walk ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define walk
  (λ (v s)
    ; pr: (v var) | (v val) | #f
    (let ([pr (and (var? v)
                   (assp (λ (v₂) (var=? v v₂)) s))])
      (if pr (walk (cdr pr) s) v))))

(define walk*
  (λ (v s)
    (let ([v (walk v s)])
      (cond
        [(var? v) v]
        [(pair? v)
         (cons (walk* (car v) s)
               (walk* (cdr v) s))]
        [else v]))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; unify ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define occurs?
  (λ (v₁ v₂ s)
    (let ([v₂ (walk v₂ s)])
      (cond
        [(var? v₂) (eqv? v₁ v₂)]
        [(pair? v₂) (or (occurs? v₁ (car v₂) s)
                        (occurs? v₁ (cdr v₂) s))]
        [else #f]))))

(define unify
  (λ (v₁ v₂ s)
    (let ([v₁ (walk v₁ s)] [v₂ (walk v₂ s)])
      (cond
        [(and (var? v₁) (var? v₂) (var=? v₁ v₂)) s]
        [(var? v₁) (if (occurs? v₁ v₂ s)
                       #f
                       `((,v₁ . ,v₂) . ,s))]
        [(var? v₂) (if (occurs? v₂ v₁ s)
                       #f
                       `((,v₂ . ,v₁) . ,s))]
        [(and (pair? v₁) (pair? v₂))
         (let ([s (unify (car v₁) (car v₂) s)])
           (and s (unify (cdr v₁) (cdr v₂) s)))]
        [else (and (eqv? v₁ v₂) s)]))))

; s∧d = ø   => #t
; s∧d ≠ ø   => #f
(define validate-d
  (λ (s d)
    (if (null? s)
        #t
        (let ([sh (car s)])
          (let ([v (car sh)]
                [v₁ (cdr sh)])
            (let ([v₂ (walk v d)])
              (cond
                [(eqv? v₁ v₂) #f]
                [else (validate-d (cdr s) d)])))))))

; check type
(define validate-t
  (λ (s t)
    (if (null? s)
        #t
        (let ([sh (car s)])
          (let ([v (car sh)]
                [v₁ (cdr sh)])
            (let ([pred? (walk v t)])
              (cond
                [(eqv? v pred?) (validate-t (cdr s) t)]
                [(pred? v₁) (validate-t (cdr s) t)]
                [else #f])))))))

; s₁ - s₂
(define minus
  (λ (s₁ s₂)
    (if (null? s₁)
        '()
        (let ([sh (car s₁)])
          (let ([v (car sh)]
                [v₁ (cdr sh)])
            (let ([v₂ (walk v s₂)])
              (cond
                [(eqv? v₁ v₂)
                 (minus (cdr s₁) s₂)]
                [else (cons sh (minus (cdr s₁) s₂))])))))))

(define :s car)
(define :d cadr)
(define :c caddr)
(define :t cadddr)
(define empty-state '(() () 0 ()))

(define :u₁ car)
(define :u₂ cdr)
(define unit₀
  (λ (s/d/c/t) (cons s/d/c/t '())))

; (var var) -> s/d/c/t -> unit/null
(define ==
  (λ (v₁ v₂)
    (λ (s/d/c/t)
      (let ([s (unify v₁ v₂ (:s s/d/c/t))])
        (if s
            (let ([d (validate-d s (:d s/d/c/t))]
                  [t (validate-t s (:t s/d/c/t))]) 
              (if (and d t)
                  (unit₀ `(,s . ,(cdr s/d/c/t)))
                  '()))
            '())))))
; (var var) -> s/d/c/t -> unit/null
(define =/=
  (λ (v₁ v₂)
    (λ (s/d/c/t)
      (let ([s (:s s/d/c/t)] [d (:d s/d/c/t)]
            [c (:c s/d/c/t)] [t (:t s/d/c/t)])
        (let ([s₁ (unify v₁ v₂ s)])
          (if s₁
              (if (= (length s) (length s₁))
                  '()
                  (unit₀ `(,s (,@(minus s₁ s) . ,d) ,c ,t)))
              (unit₀ s/d/c/t)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; type ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define typeo
  (λ (pred v)
    (λ (s/d/c/t)
      (let ([v (walk v (:s s/d/c/t))]
            [t (:t s/d/c/t)])
        (cond
          [(var? v) (let ([v-type (walk v t)])
                      (cond
                        [(procedure? v-type)
                         (if (eqv? v-type pred) (unit₀ s/d/c/t) '())]
                        [else (unit₀ `(,(:s s/d/c/t)
                                       ,(:d s/d/c/t)
                                       ,(:c s/d/c/t)
                                       ((,v . ,pred) . ,t)))]))]
          [(pred v) (unit₀ s/d/c/t)]
          [else '()])))))

(define booleano
  (λ (v) (typeo boolean? v)))

(define numbero
  (λ (v) (typeo number? v)))

(define symbolo
  (λ (v) (typeo symbol? v)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; fresh ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (var -> s/d/c/t -> unit/null) -> s/d/c/t -> unit/null
(define call/fresh
  (λ (f)
    (λ (s/d/c/t)
      (let ([c (:c s/d/c/t)])
        ((f (var c)) `(,(:s s/d/c/t) ,(:d s/d/c/t) ,(add1 c) ,(:t s/d/c/t)))))))

#|
> (define empty-state '(() () 0))
> (let ([$ ((call/fresh (lambda (q) (== q 5))) empty-state)])
        (car $))
(((#(0) . 5)) () 1)
> (let ([$ ((call/fresh (lambda (q) (=/= q 5))) empty-state)])
          (car $))
(() ((#(0) . 5)) 1)
|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; wrappers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; $ ----> unit/null
;     |   (cons s/d/c/t $)
;     |   (lambda () $)
; (s/d/c/t -> unit/null) (s/d/c/t -> unit/null) -> s/d/c/t -> $
(define disj
  (λ (g₁ g₂)
    (λ (s/d/c/t)
      (mplus (g₁ s/d/c/t) (g₂ s/d/c/t)))))
; (s/d/c/t -> unit/null) (s/d/c/t -> unit/null) -> s/d/c/t -> $
(define conj
  (λ (g₁ g₂)
    (λ (s/d/c/t)
      (bind (g₁ s/d/c/t) g₂))))
; ($ $) -> $
(define mplus
  (λ ($₁ $₂)
    (cond
      [(null? $₁) $₂]
      [(procedure? $₁) (λ () (mplus $₂ ($₁)))]
      [else (cons (:u₁ $₁) (mplus (:u₂ $₁) $₂))])))
; ($ g) -> $
(define bind
  (λ ($ g)
    (cond
      [(null? $) '()]
      [(procedure? $) (λ () (bind ($) g))]
      [else (mplus (g (:u₁ $)) (bind (:u₂ $) g))])))

(define-syntax Zzz
  (syntax-rules ()
    [(_ g) (λ (s/d/c/t) (λ () (g s/d/c/t)))]))

(define-syntax conj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g₀ g ...) (conj (Zzz g₀) (conj+ g ...))]))

(define-syntax disj+
  (syntax-rules ()
    [(_ g) (Zzz g)]
    [(_ g₀ g ...) (disj (Zzz g₀) (disj+ g ...))]))

(define-syntax conde
  (syntax-rules ()
    [(_ (g₀ g ...) ...) (disj+ (conj+ g₀ g ...) ...)]))

(define-syntax fresh
  (syntax-rules ()
    [(_ () g₀ g ...) (conj+ g₀ g ...)]
    [(_ (x₀ x ...) g₀ g ...)
     (call/fresh
       (λ (x₀)
         (fresh (x ...) g₀ g ...)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; run ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-syntax run
  (syntax-rules ()
    [(_ n (x ...) g₀ g ...)
     (map reify-1st (take n ((fresh (x ...) g₀ g ...) empty-state)))]))

(define-syntax run*
  (syntax-rules ()
    [(_ (x ...) g₀ g ...)
     (map reify-1st (take-all ((fresh (x ...) g₀ g ...) empty-state)))]))

(define take
  (λ (n $)
    (if (zero? n)
        '()
        (let ([$ (pull $)])
          (if (null? $)
              '()
              (cons (:u₁ $) (take (sub1 n) (:u₂ $))))))))

(define take-all
  (λ ($)
    (let ([$ (pull $)])
      (if (null? $)
          '()
          (cons (:u₁ $) (take-all (:u₂ $)))))))

(define pull
  (λ ($)
    (if (procedure? $)
        (pull ($))
        $)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; reify ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define reify-1st
  (λ (s/d/c/t)
    (let ([v (walk* (var 0) (:s s/d/c/t))])
      (walk* v (reify-s v '())))))

(define reify-s
  (λ (v s)
    (let ([v (walk v s)])
      (cond
        [(var? v)
         (let ([n (reify-name (length s))])
           (cons `(,v . ,n) s))]
        [(pair? v) (reify-s (cdr v) (reify-s (car v) s))]
        [else s]))))

(define reify-name
  (λ (n)
    (string->symbol
      (string-append "_" (number->string n)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; test ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define appendo
  (λ (l s out)
    (conde
      [(== '() l) (== s out)]
      [(fresh (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendo d s res))])))

#|
> (run* (q) (fresh (x y) (== `(,x ,y) q) (appendo x y '(1 2 3 4 5))))
((() (1 2 3 4 5))
 ((1) (2 3 4 5))
 ((1 2) (3 4 5))
 ((1 2 3) (4 5))
 ((1 2 3 4) (5))
 ((1 2 3 4 5) ()))
> (run* (q) (=/= 2 q))
(_0)
> (run* (q) (=/= 2 q) (== 2 q))
()
> (run* (q) (conde ((=/= 2 q)) ((== 2 q))))
(_0 2)
|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; type infer ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define lookup
  (λ (G e t)
    (fresh (e^ t^ G^)
      (== `((,e^ . ,t^) . ,G^) G)
      (conde
        [(== e^ e) (== t^ t)]
        [(=/= e^ e) (lookup G^ e t)]))))

(define !-
  (λ (G e t)
    (conde
      [(numbero e) (== 'Nat t)]
      [(== t 'Bool)
       (conde
         [(== #t e)]
         [(== #f e)])]
      [(fresh (e₁)
       (== `(not ,e₁) e)
       (== 'Bool t)
       (!- G e₁ 'Bool))]
      [(fresh (e₁)
       (== `(zero? ,e₁) e)
       (== 'Bool t)
       (!- G e₁ 'Nat))]
      [(fresh (e₁)
       (== `(sub1 ,e₁) e)
       (== 'Nat t)
       (!- G e₁ 'Nat))]
      [(fresh (ne₁ ne₂)
       (== `(+ ,ne₁ ,ne₂) e)
       (== 'Nat t)
       (!- G ne₁ 'Nat)
       (!- G ne₂ 'Nat))]
      [(fresh (ne₁ ne₂)
       (== `(* ,ne₁ ,ne₂) e)
       (== 'Nat t)
       (!- G ne₁ 'Nat)
       (!- G ne₂ 'Nat))]
      [(fresh (teste conseqe alte)
       (== `(if ,teste ,conseqe ,alte) e)
       (!- G teste 'Bool)
       (!- G conseqe t)
       (!- G alte t))]
      [(symbolo e) (lookup G e t)]
      [(fresh (x b)
       (== `(fix (lambda (,x) ,b)) e)
       (symbolo x)
       (!- `((,x . ,t) . ,G) b t))]
      [(fresh (e₁ e₂ t₁ t₂)
       (== `(cons ,e₁ ,e₂) e)
       (== `(pairof ,t₁ ,t₂) t)
       (!- G e₁ t₁)
       (!- G e₂ t₂))]
      [(fresh (ls)
       (== `(car ,ls) e)
       (fresh (t₂)
         (!- G ls `(pairof ,t ,t₂))))]
      [(fresh (ls)
       (== `(cdr ,ls) e)
       (fresh (t₂)
         (!- G ls `(pairof ,t₂ ,t))))]
      [(fresh (x b)
       (== `(lambda (,x) ,b) e)
       (symbolo x)
       (fresh (tx tb)
         (== `(,tx -> ,tb) t)
         (!- `((,x . ,tx) . ,G) b tb)))]
      [(fresh (e₁ arg)
       (== `(,e₁ ,arg) e)
       (fresh (targ)
         (!- G e₁ `(,targ -> ,t))
         (!- G arg targ)))])))

#|
> (run* (q) (!- '() #t q))
(Bool)
> (run* (q) (!- '() 17 q))
(Nat)
> (run* (q) (!- '() '(zero? 24) q))
(Bool)
> (run* (q) (!- '() '(zero? (sub1 24)) q))
(Bool)
> (run* (q) (!- '() '(not (zero? (sub1 24))) q))
(Bool)
> (run* (q)
      (!- '() '(zero? (sub1 (sub1 18))) q))
(Bool)
> (run* (q)
      (!- '()  '(lambda (n) (if (zero? n) n n)) q))
((Nat -> Nat))
> (run* (q)
      (!- '() '((lambda (n) (zero? n)) 5) q))
(Bool)
> (run* (q)
      (!- '() '(if (zero? 24) 3 4) q))
(Nat)
> (run* (q)
      (!- '() '(if (zero? 24) (zero? 3) (zero? 4)) q))
(Bool)
> (run* (q)
      (!- '() '(lambda (x) (sub1 x)) q))
((Nat -> Nat))
> (run* (q)
      (!- '() '(lambda (a) (lambda (x) (+ a x))) q))
((Nat -> (Nat -> Nat)))
> (run* (q)
      (!- '() '(lambda (f)
                 (lambda (x)
                   ((f x) x)))
           q))
(((_0 -> (_0 -> _1)) -> (_0 -> _1)))
> (run* (q)
      (!- '() '(sub1 (sub1 (sub1 6))) q))
(Nat)
> (run 1 (q)
      (fresh (t)
        (!- '() '(lambda (f) (f f)) t)))
()
> (length (run 20 (q)
               (fresh (lam a b)
                 (!- '() `((,lam (,a) ,b) 5) 'Nat)
                 (== `(,lam (,a) ,b) q))))
20
> (length (run 30 (q) (!- '() q 'Nat)))
30
> (length (run 30 (q) (!- '() q '(Nat -> Nat))))
30
> (length (run 500 (q) (!- '() q '(Nat -> Nat))))
500
> (length (run 30 (q) (!- '() q '(Bool -> Nat))))
30
> (length (run 30 (q) (!- '() q '(Nat -> (Nat -> Nat)))))
30
> (length (run 100 (q)
               (fresh (e t)
                 (!- '() e t)
                 (== `(,e ,t) q))))
100
> (length (run 100 (q)
               (fresh (g e t)
                 (!- g e t)
                 (== `(,g ,e ,t) q))))
100
> (length
     (run 100 (q)
       (fresh (g v)
         (!- g `(var ,v) 'Nat)
         (== `(,g ,v) q))))
100
> (run 1 (q)
    (fresh (g)
      (!- g
        '((fix (lambda (!)
                 (lambda (n)
                   (if (zero? n)
                       1
                       (* n (! (sub1 n)))))))
          5)
        q)))
(Nat)
> (run 1 (q)
    (fresh (g)
      (!- g
        '((fix (lambda (!)
                 (lambda (n)
                   (* n (! (sub1 n))))))
          5)
        q)))
(Nat)
> (run* (q)
      (!- '() '(cons (zero? 1) (zero? 0)) q))
((pairof Bool Bool))
> (run* (q)
      (!- '() '(cons (zero? 1) (cons (zero? 1) (zero? 0))) q))
((pairof Bool (pairof Bool Bool)))
> (run* (t)
      (!- '() '(lambda (x) (cons x x)) t))
((_0 -> (pairof _0 _0)))
> (run* (t)
      (!- '() '(lambda (x) (lambda (y) (cons (zero? x) (+ x y)))) t))
((Nat -> (Nat -> (pairof Bool Nat))))
> (run* (t) (!- '() '(lambda (x) (zero? (car x))) t))
(((pairof Nat _0) -> Bool))
> (run* (t) (!- '() '(lambda (x) (car x)) t))
(((pairof _0 _1) -> _0))
> (run* (t)
      (!- '() '((lambda (x) (zero? (car x))) (cons 0 1)) t))
(Bool)
> (run* (t) (!- '() '((lambda (x) (zero? (car x))) (cons 0 #f)) t))
(Bool)
> (run* (t)
      (!- '() '((lambda (x) (zero? (car x))) (cons #f 0)) t))
()
> (run* (t)
      (!- '() '(lambda (x) (zero? (cdr x))) t))
(((pairof _0 Nat) -> Bool))
> (run* (t)
      (!- '() '(lambda (x) (cdr x)) t))
(((pairof _0 _1) -> _1))
> (run* (t)
      (!- '() '((lambda (x) (zero? (cdr x))) (cons 0 1)) t))
(Bool)
> (run* (t)
      (!- '() '((lambda (x) (zero? (cdr x))) (cons 0 #f)) t))
()
> (run* (t)
      (!- '() '((lambda (x) (zero? (cdr x))) (cons #f 0)) t))
(Bool)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; interface ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define infer
  (λ (p) (run* (t) (!- '() p t))))
