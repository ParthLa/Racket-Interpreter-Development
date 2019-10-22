#lang racket
(require racket/struct)
(provide (all-defined-out))
(require "defs.rkt")
(require "examples.rkt")

(define stacks (make-vector 100))
(define stacksindex 0)

(define (zip l1 l2)
  (cond [(null? l1) l1]
        [(null? l2) l2]
        [else (cons (cons (car l1) (car l2)) (zip (cdr l1) (cdr l2)))]))

(struct node(t1 t2) #:transparent)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;Global definitions. A counter that tracks the framenumber.
(define framenumber 0)


;The stack and its operations. I have decided to make the stack a global.
(define stack '())
(define (push frame) (set! stack (cons frame stack)))
(define (pop) (if (null? stack) (error "Empty stack")
                        (set! stack (cdr stack))))
(define (top) (if (null? stack) (error "Empty stack")
                        (car stack)))


;createframe creates a new frame. It gets its number from
;;framenumber and as a side effect increases framenumber
(define (createframe hashtable parent);hastable gives the initial bindings
  (begin (let ([f (frame framenumber hashtable parent)]) (set! framenumber (+ 1 framenumber)) f)))
   

;This creates the global frame, which, in our case, contains
;empty bindings.
(push (createframe (make-hash '()) (emptyframe)))

;This interprets a program. It uses the following function processdef.
(define (eval-program prog)
         (match prog
           [(pgm '()) (return-value-of-main (top))]
           [(pgm deflist) (begin (processdef (car deflist) (top))
                                 (eval-program (pgm (cdr deflist))))]))

;;processdef describes how each definition is processed and added to
;;the frame fr.
(define (processdef defn fr)
 (match defn    
 [(def v/f exp) (let ([bind-pair (cons v/f (eval-exp exp))])
        (addn bind-pair fr))]))

(define (addn bind-pair fr)
  (match fr
  [(frame number bindings parent) ;(set! bindings (make-hash (cons bind-pair (hash->list bindings))))
                                  (hash-set! bindings (car bind-pair) (cdr bind-pair))]))

;; We have said that the result of the program is the value of
;; the symbol main. main must be a defined symbol in each program.
(define (return-value-of-main frame)
  (hash-ref! (frame-bindings frame) 'main "main not found"))



;; The expression evaluator is the heart of the interpreter.
;; It will use the functions below
(define (eval-exp exp)

 (cond [(symbol? exp) (let ([required-frame (search exp (top))])
                        (if (equal? required-frame (emptyframe)) (error "Symbol not found")
                            (hash-ref (frame-bindings required-frame) exp)))] ;improvise here
        [(boolean? exp) exp]
        [(number? exp) exp]
        [(list? exp) exp]
        [(string? exp) exp]
        [else (match exp
               [(uexp op exp1) (op (eval-exp exp1))]
               [(bexp op exp1 exp2) (op (eval-exp exp1) (eval-exp exp2))]
               [(lam var body) (closure (lam var body) (top))]                                          ;..assuming the variable list of lambda will be used as it is...
               [(app exp1 explist) (match (eval-exp exp1)
                                     [(closure (lam l1 body) frame)
                                    (begin (push (createframe (make-hash (zip l1 (map eval-exp explist))) frame)) ; frame here is the one in which exp1 was defined. 
                                              (begin0 (eval-exp body) (pop)))])]
                
               [(iff cond exp1 exp2) (if (eval-exp cond) (eval-exp exp1) (eval-exp exp2))]                
               [(sett var exp1) (let ([required-frame (search var (top))])
                                  (if (emptyframe? required-frame) (error "Symbol not found")
                                      (hash-set! (frame-bindings required-frame) var (eval-exp exp1))))] ; assuming no change in current-frame during set! and var to be a symbol
                [(lett deflist exp1) (push (createframe (make-hash (map cons
                                                                        (map def-var/fun deflist)
                                                                        (map (λ (x) (eval-exp (def-exp x))) deflist)))
                                                                        (top))) 
                                           (let ([v (eval-exp exp1)]) (pop) v)] ; check error here
               [(lets deflist exp1) ; (if (null? deflist) (eval-exp (lett deflist exp1))
                                     ;                     (eval-exp (lett (list (car deflist)) (lets (cdr deflist) exp1))))]
                                      (eval-exp (process-lets deflist exp1))]
                                                         
               [(beginexp explist) (process-beginexp explist)]
               [(defexp deflist exp1) (if (null? deflist) (eval-exp exp1)
                                                         (begin (processdef (car deflist) (top))
                                                                (eval-exp (defexp (cdr deflist) exp1))))] ;current-frame is (top)
               [(debugexp)
                (begin
                 (vector-set! stacks stacksindex stack)
                 (set! stacksindex (+ 1 stacksindex)))])]))
               ;(debugexp) (begin (print-current-environment (top)))])]))


;;An auxilliary function that processes a begin expression
(define (process-beginexp explist)
  (if (null? (cdr explist)) (eval-exp (car explist))
      (begin (eval-exp (car explist)) (process-beginexp (cdr explist)))))

;;An auxilliary function that processes a let* expression.
;;The let* definitions are in deflist, and the let* body is exp.
(define (process-lets deflist exp)
    (if (null? deflist)  exp
        (lett (list (car deflist)) (process-lets (cdr deflist) exp))))


(define (my-hash-table deflist bind-list)
  (if (null? deflist) (make-hash bind-list)
   (match (car deflist)
    [(def v/f exp) (begin (set! bind-list (cons (cons v/f (eval-exp exp)) bind-list)) (my-hash-table (cdr deflist) bind-list))])))
  
  
      

;;Prints the current environment running through a chain of frames.
;;Note that my struct definitions are such that if fr is a frame,
;;then (displayln fr) will print the frame in the format that I have
;;shown. 
(define (print-current-environment fr) 
  (match fr
    [(frame number bindings parent) (if (equal? parent (emptyframe)) (begin (displayln "@@@@@@@@@@@@@@@@@@@@@@@")
                                                                            (displayln fr) 
                                                                            (displayln "@@@@@@@@@@@@@@@@@@@@@@@"))
                                        (begin (displayln "@@@@@@@@@@@@@@@@@@@@@@@")
                                               (displayln fr) (print-current-environment parent)))]))

;;Search for the symbol sym in an environment that starts with the frame
;;fr. We shall make search return either the  emptyframe
;;or the frame containing the symbol (note, not the value of the
;;symbol itself.

(define (search sym fr)
  (cond [(or (emptyframe? fr)
             (hash-has-key? (frame-bindings fr) sym)) fr]
        [else (search sym (frame-parent fr))]))

(define (cleanup)
  (set!  stacks (make-vector 100))
  (set! stacksindex 0)
  (set! framenumber 0)
  (set! stack '())
  (push (createframe (make-hash '()) (emptyframe))))

               


