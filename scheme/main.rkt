#lang racket/base

;; Notice
;; To install (from within the package directory):
;;   $ raco pkg install
;; To install (once uploaded to pkgs.racket-lang.org):
;;   $ raco pkg install <<name>>
;; To uninstall:
;;   $ raco pkg remove <<name>>
;; To view documentation:
;;   $ raco docs <<name>>
;;
;; For your convenience, we have included LICENSE-MIT and LICENSE-APACHE files.
;; If you would prefer to use a different license, replace those files with the
;; desired license.
;;
;; Some users like to add a `private/` directory, place auxiliary files there,
;; and require them in `main.rkt`.
;;
;; See the current version of the racket style guide here:
;; http://docs.racket-lang.org/style/index.html

;; Code here

(require racket/generic racket/match racket/contract (for-syntax racket/base))
(provide (struct-out exn:fail:scheme)
         (struct-out exn:fail:scheme:syntax)
         (struct-out exn:fail:scheme:syntax:primitive)
         (struct-out exn:fail:scheme:syntax:unbound)
         (struct-out exn:fail:scheme:application)
         (struct-out exn:fail:scheme:application:arity)
         (struct-out exn:fail:scheme:application:applicable)

         (struct-out __void)

         scheme-self-evaluating? scheme-variable? scheme-procedure?

         default-representation?
         (rename-out (make-if default:make-if)
                     (make-set! default:make-set!)
                     (make-begin default:make-begin)
                     (make-quote default:make-quote)
                     (make-lambda default:make-lambda)
                     (make-define default:make-define)
                     (make-expression default:make-expression))

         gen:if-form
         gen:define-form
         gen:set!-form
         gen:begin-form
         gen:quote-form
         gen:lambda-form
         gen:s-exp

         (contract-out
          #:exists env?
          (make-primitive (-> procedure? exact-nonnegative-integer? any))
          (make-env (->* ((listof (cons/c symbol? any/c))) (#:expander (-> any/c (-> all-implement/c any) any)) env?))
          (expand-scheme (-> all-implement/c env? any))
          (eval-scheme (-> all-implement/c env? any))
          (apply-scheme (-> any/c list? any))))

;;Exceptions
(struct exn:fail:scheme exn:fail ())
(struct exn:fail:scheme:syntax exn:fail:scheme ())
(struct exn:fail:scheme:syntax:primitive exn:fail:scheme:syntax ())
(struct exn:fail:scheme:syntax:unbound exn:fail:scheme:syntax ())
(struct exn:fail:scheme:application exn:fail:scheme ())
(struct exn:fail:scheme:application:arity exn:fail:scheme:application ())
(struct exn:fail:scheme:application:applicable exn:fail:scheme:application ())

;;Macros
(define-syntax (check-and-extract-form stx)
  (syntax-case stx ()
    ((_ val (pattern id) ...)
     #'(match val
         (pattern id)
         ...
         (_ (raise (exn:fail:scheme:syntax:primitive (format "Malformed scheme form: ~s" val) (current-continuation-marks))))))
    ((_ val pattern id)
     #'(match val
         (pattern id)
         (_ (raise (exn:fail:scheme:syntax:primitive (format "Malformed scheme form: ~s" val) (current-continuation-marks))))))))

;;Structures
(struct __primitive (proc arity) #:constructor-name make-primitive)
(struct __closure (env arity args body))
(struct __operand (num list))
(struct __void ())
(struct __expander_box (expression))
(struct __environment (frames expander))
(struct __thunk (exp env (arg #:auto) (run? #:auto)) #:mutable #:auto-value #f)

;;Constants
(define _void (__void))

;;Utilities
(define (non-empty-list? l) (and (list? l) (not (null? l))))
(define (check-primitive-part n v pred) (cond ((pred v) v) (else (raise (exn:fail:scheme:syntax:primitive (format "Malformed ~a: ~s" n v) (current-continuation-marks))))))
(define (raise-arity args vals) (raise (exn:fail:scheme:application:arity (format "Arity mismatch:\nexpected: ~a\nactual: ~a" args vals) (current-continuation-marks))))

;;Representation
;;General predicates
(define (scheme-self-evaluating? v) (or (number? v) (boolean? v) (bytes? v) (__void? v)))
(define (scheme-variable? v) (symbol? v))
(define (scheme-procedure? v) (or (__primitive? v) (__closure? v) (__thunk? v)))
;;Default representation
(define (default-representation? f)
  (non-empty-list? f))
(define (make-define id val) (list 'define id val))
(define (make-set! id val) (list 'set! id val))
(define (make-lambda args body) (cons 'lambda (cons args body)))
(define (make-begin body) (cons 'begin body))
(define (make-quote datum) (list 'quote datum))
(define (make-if test first second) (list 'if test first second))
(define (make-expression operator operand) (cons operator operand))

;;Frames
(define (make-frame assocs) (make-hasheq assocs))
(define ((make-frame-setter val) t id) (hash-set! t id val) _void)
(define (has-id? frame id) (hash-has-key? frame id))
(define (set-frame! frame id val) (hash-set! frame id val))
(define (refer-frame frame id) (hash-ref frame id))
;;Environments
(define (make-env (assocs null) #:expander (expander (lambda _ #f))) (__environment (list (make-frame assocs)) expander))
(define (add-frame env assocs) (struct-copy __environment env (frames (cons (make-frame assocs) (__environment-frames env)))))
(define (refer-env env id #:proc (proc refer-frame))
  (let/cc return
    (for ((t (in-list (__environment-frames env))))
      (cond ((has-id? t id) (return (proc t id)))))
    (raise (exn:fail:scheme:syntax:unbound (format "~a is not bound" id) (current-continuation-marks)))))
(define (env-expand form env) ((__environment-expander env) form __expander_box))
(define (set-env! env id val) (set-frame! (car (__environment-frames env)) id val) _void)

;;Data-directed dispatching
;;--------------------------
;;Special forms
;;Only syntax are checked here
(define-generics define-form
  (define? define-form)
  (define-id define-form)
  (define-val define-form)
  #:defined-predicate define-implement?
  #:fast-defaults ((default-representation?
                     (define (define? l) (eq? 'define (car l)))
                     (define (define-id f) (check-and-extract-form f (list 'define id _) id))
                     (define (define-val f) (check-and-extract-form f (list 'define _ val) val)))))
(define-generics set!-form
  (set!? set!-form)
  (set!-id set!-form)
  (set!-val set!-form)
  #:defined-predicate set!-implement?
  #:fast-defaults ((default-representation?
                     (define (set!? l) (eq? 'set! (car l)))
                     (define (set!-id f) (check-and-extract-form f (list 'set! id _) id))
                     (define (set!-val f) (check-and-extract-form f (list 'set! _ val) val)))))
(define-generics lambda-form
  (lambda? lambda-form)
  (lambda-args lambda-form)
  (lambda-body lambda-form)
  #:defined-predicate lambda-implement?
  #:fast-defaults ((default-representation?
                     (define (lambda? l) (eq? 'lambda (car l)))
                     (define (lambda-args f) (check-and-extract-form f (list 'lambda (list args ...) _ ...) args))
                     (define (lambda-body f) (check-and-extract-form f (list 'lambda (list _ ...) body ...) body)))))
(define-generics begin-form
  (begin? begin-form)
  (begin-body begin-form)
  #:defined-predicate begin-implement?
  #:fast-defaults ((default-representation?
                     (define (begin? l) (eq? 'begin (car l)))
                     (define (begin-body f) (check-and-extract-form f (list 'begin body ...) body)))))
(define-generics quote-form
  (quote? quote-form)
  (quote-datum quote-form)
  #:defined-predicate quote-implement?
  #:fast-defaults ((default-representation?
                     (define (quote? l) (eq? 'quote (car l)))
                     (define (quote-datum f) (check-and-extract-form f (list 'quote datum) datum)))))
(define-generics if-form
  (if? if-form)
  (if-test if-form)
  (if-first-branch if-form)
  (if-second-branch if-form)
  #:defined-predicate if-implement?
  #:fast-defaults ((default-representation?
                     (define (if? l) (eq? 'if (car l)))
                     (define (if-test f) (check-and-extract-form f (list 'if test first second) test))
                     (define (if-first-branch f) (check-and-extract-form f (list 'if test first second) first))
                     (define (if-second-branch f) (check-and-extract-form f ((list 'if test first second) second) ((list 'if test first) #f))))))

;;Scheme expression
(define-generics s-exp
  (expression? s-exp)
  (expression-operator s-exp)
  (expression-operand s-exp)
  #:defined-predicate s-exp-implement?
  #:fast-defaults ((default-representation?
                     (define (expression? _) #t) ;;A non-empty list can always be considered as an expression
                     (define (expression-operator l) (car l))
                     (define (expression-operand l) (cdr l)))))

;;Contracts
(define all-implement/c (and/c define-implement?
                               set!-implement?
                               begin-implement?
                               if-implement?
                               quote-implement?
                               lambda-implement?
                               s-exp-implement?))

;;Selectors with result checking
(define (n:define-id f) (check-primitive-part 'identifier (define-id f) scheme-variable?))
(define (n:define-val f) (define-val f))
(define (n:set!-id f) (check-primitive-part 'identifier (set!-id f) scheme-variable?))
(define (n:set!-val f) (set!-val f))
(define (n:begin-body f) (check-primitive-part '|begin body| (begin-body f) non-empty-list?))
(define (n:lambda-args f) (check-primitive-part 'arguments (lambda-args f) (listof (or/c scheme-variable? (list/c scheme-variable? (or/c 'lazy 'lazy-memo))))))
(define (n:lambda-body f) (check-primitive-part '|lambda body| (lambda-body f) non-empty-list?))
(define (n:if-test f) (if-test f))
(define (n:if-first f) (if-first-branch f))
(define (n:if-second f) (if-second-branch f))
(define (n:quote-datum f) (quote-datum f))
(define (n:expression-operator f) (expression-operator f))
(define (n:expression-operand f) (check-primitive-part 'operands (expression-operand f) list?))
;;--------------------------

;;Arity handling
;;Operands
(define (make-operand lst)
  (__operand (length lst) lst))
(define (map-operand p o)
  (struct-copy __operand o (list (map p (__operand-list o)))))
(define (get-operand-nums o)
  (if (list? o) (length o) (__operand-num o)))
(define (get-operand-list o)
  (if (list? o) o (__operand-list o)))
;;Procedures
(define (make-closure env args body)
  (__closure env (length args) args body))
(define (get-procedure-arity p)
  (cond ((__primitive? p) (__primitive-arity p))
        ((__closure? p) (__closure-arity p))
        (else 0)))

;;Argument handling
(define (lazy-argument? a)
  (and (list? a) (or (eq? (cadr a) 'lazy) (eq? (cadr a) 'lazy-memo))))
(define (lazy-memo-argument? a)
  (and (list? a) (eq? (cadr a) 'lazy-memo)))
(define (argument-name a)
  (if (scheme-variable? a) a (car a)))
;;Thunks
(define (delay-it o e)
  (__thunk o e))
(define (add-arg-to-thunk arg thunk)
  (set-__thunk-arg! thunk arg)
  thunk)
(define (actual-value t) ;;Get the result anyway, no matter whether the argument field is set
  (define (evaluated-thunk? t) (__thunk-run? t))
  (cond ((evaluated-thunk? t) (__thunk-exp t))
        (else (define result ((__thunk-exp t) (__thunk-env t)))
              (cond ((lazy-memo-argument? (__thunk-arg t))
                     (set-__thunk-run?! t #t)
                     (set-__thunk-exp! t result)
                     ;;Garbage collection
                     (set-__thunk-env! t #f)))
              result)))
(define (force-it v)
  (if (__thunk? v) (actual-value v) v))

;;Expansion, evaluation and application
(define-values (expand-scheme eval-scheme apply-scheme)
  (letrec ((expand-scheme
            (lambda (f e)
              (cond ((let ((expanded (env-expand f e)))
                       (if (__expander_box? expanded)
                           expanded
                           #f))
                     =>
                     ;;You have to handle identifiers yourself
                     (lambda (b) (expand-scheme (__expander_box-expression b) e)))
                    ((or (scheme-variable? f) (scheme-self-evaluating? f)) f)
                    ;;Several representations can be mixed
                    ((if? f) (make-if (expand-scheme (n:if-test f) e)
                                      (expand-scheme (n:if-first f) e)
                                      (expand-scheme (n:if-second f) e)))
                    ((define? f) (make-define (n:define-id f)
                                              (expand-scheme (n:define-val f) e)))
                    ((set!? f) (make-set! (n:set!-id f) (expand-scheme (n:set!-val f) e)))
                    ((begin? f) (make-begin (map (lambda (f) (expand-scheme f e)) (n:begin-body f))))
                    ((lambda? f) (make-lambda (n:lambda-args f) (map (lambda (f) (expand-scheme f e)) (n:lambda-body f))))
                    ((quote? f) f)
                    ((expression? f) (make-expression (expand-scheme (n:expression-operator f) e)
                                                      (map (lambda (f) (expand-scheme f e)) (n:expression-operand f))))
                    (else (raise (exn:fail:scheme:syntax (format "Malformed form: ~s" f) (current-continuation-marks)))))))

           ;;Syntax analysis
           ;;These functions are not exported
           (analyze-sequence
            (lambda (seq)
              (define (sequentially first then)
                (lambda (env) (first env) (then env)))
              (define (loop first rest)
                (if (null? rest)
                    first
                    (loop (sequentially first (car rest))
                          (cdr rest))))
              (loop (analyze-primitive-form (car seq)) (map analyze-primitive-form (cdr seq)))))
           (analyze-primitive-form
            (lambda (exp)
              (cond ((scheme-self-evaluating? exp) (lambda (_) exp))
                    ((scheme-variable? exp) (lambda (env) (refer-env env exp)))

                    ((if? exp)
                     (define test (analyze-primitive-form (n:if-test exp)))
                     (define then (analyze-primitive-form (n:if-first exp)))
                     (define alter (analyze-primitive-form (n:if-second exp)))
                     (lambda (env)
                       (if (test env)
                           (then env)
                           (alter env))))
                    ((quote? exp)
                     (define datum (n:quote-datum exp))
                     (lambda (_) datum))
                    ((begin? exp)
                     (define seq (n:begin-body exp))
                     (analyze-sequence seq))
                    ((lambda? exp)
                     (define args (n:lambda-args exp))
                     (define body (analyze-sequence (n:lambda-body exp)))
                     (lambda (env)
                       (make-closure env args body)))
                    ((set!? exp)
                     (define id (n:set!-id exp))
                     (define val (analyze-primitive-form (n:set!-val exp)))
                     (lambda (env) (refer-env env id #:proc (make-frame-setter (val env)))))
                    ((define? exp)
                     (define id (n:define-id exp))
                     (define val (analyze-primitive-form (n:define-val exp)))
                     (lambda (env)
                       (set-env! env id (val env))))

                    ((expression? exp)
                     (define operator (analyze-primitive-form (n:expression-operator exp)))
                     (define operand (make-operand (map analyze-primitive-form (n:expression-operand exp))))
                     (lambda (env)
                       (apply-scheme (operator env) (map-operand (lambda (o) (delay-it o env)) operand))))

                    (else (raise (exn:fail:scheme:syntax (format "Malformed form: ~s" exp)) (current-continuation-marks))))))

           (eval-primitive-form (lambda (exp env) ((analyze-primitive-form exp) env)))

           (apply-scheme
            (lambda (operator operand)
              ;;Checking
              (cond ((not (scheme-procedure? operator))
                     (raise (exn:fail:scheme:application:applicable (format "~s is not an applicable object" operator) (current-continuation-marks))))
                    ((not (= (get-procedure-arity operator) (get-operand-nums operand)))
                     (raise-arity (get-procedure-arity operator) (get-operand-nums operand))))
              ;;Application
              (cond ((__primitive? operator)
                     (apply (__primitive-proc operator) (map force-it (get-operand-list operand))))
                    ((__thunk? operator) (actual-value operator))
                    (else
                     (define (cons-arg-val argument delayed)
                       (cons (argument-name argument)
                             (if (lazy-argument? argument)
                                 (cond ((__thunk? delayed) (add-arg-to-thunk argument delayed))
                                       ;;Constants
                                       (else (add-arg-to-thunk (list (argument-name argument) 'lazy-memo) (delay-it (lambda (_) delayed) #f))))
                                 (force-it delayed))))
                     (define env (add-frame (__closure-env operator) (map cons-arg-val (__closure-args operator) (get-operand-list operand))))
                     ((__closure-body operator) env))))))
    (values expand-scheme (lambda (exp env) (eval-primitive-form (expand-scheme exp env) env)) apply-scheme)))

(module* namespace racket/base
  (require rackunit racket/list racket/stream racket/match (submod ".."))
  (provide (all-from-out rackunit racket/list racket/stream racket/match racket/base (submod ".."))))

(module+ test
  ;; Any code in this `test` submodule runs when this file is run using DrRacket
  ;; or with `raco test`. The code here does not run when this file is
  ;; required by another module.

  (require racket/runtime-path racket/pretty (submod ".." namespace))

  ;;Predicates
  (check-true (default-representation? (default:make-expression '+ '(1 2))))
  (check-true (scheme-self-evaluating? 1.2))
  (check-false (scheme-procedure? +))
  (check-true (scheme-procedure? (make-primitive + 2)))
  (check-true (expression? (default:make-expression '+ '(2 2))))
  ;;Exceptions
  (check-not-exn (lambda () (expand-scheme (list (list 1)) (make-env null))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (n:set!-id (default:make-set! '(+ 1 2) 3))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (n:lambda-args (default:make-lambda '(+ 1) '((+ 1 2))))))
  (check-exn exn:fail:scheme:syntax:unbound? (lambda () (eval-scheme '(+) (make-env null))))
  (check-exn exn:fail:scheme:application:applicable? (lambda () (eval-scheme '(+) (make-env (list (cons '+ 0))))))
  (check-exn exn:fail:scheme:application:arity? (lambda () (eval-scheme '((lambda (n) (+ n 1))) (make-env (list (cons '+ (make-primitive + 2)))))))
  ;;Selectors
  (check-eq? (n:define-id (default:make-define 'a 1)) 'a)
  (check-equal? (n:if-test (default:make-if '(+ 1 2) 1 2)) '(+ 1 2))
  (check-equal? (n:quote-datum (default:make-quote '(1 . 2))) '(1 . 2))
  ;;Expansion, evaluation and application
  (define (or-matcher exp cons)
    (match exp
      ((list 'or clauses ...)
       (cons (foldl (lambda (c i) (default:make-if c c i)) #f (reverse clauses))))
      (_ #f)))
  (define env (make-env (list
                         (cons '+ (make-primitive + 2))
                         (cons '* (make-primitive * 2))
                         (cons '/ (make-primitive / 2))
                         (cons '= (make-primitive = 2))
                         (cons 'car (make-primitive car 1))
                         (cons 'cdr (make-primitive cdr 1))
                         (cons 'cons (make-primitive cons 2))
                         (cons 'list (make-primitive list 2))
                         (cons 'null null)
                         (cons 'null? (make-primitive null? 1))
                         (cons 'apply (make-primitive apply-scheme 2)))
                        #:expander or-matcher))
  (check-true
   (=
    (eval-scheme
     '(begin
        (define map (lambda (proc l)
                      (if (null? l)
                          null
                          (cons (proc (car l)) (map proc (cdr l))))))
        (apply + (map (lambda (v) (* v (+ v -1))) (list 1 2))))
     env)
    2))
  (check-true (= (apply-scheme (eval-scheme '(lambda (a) (set! a 1) a) env) (list 0)) 1))
  (check-equal? (expand-scheme '(or (= 1 2) (= 2 2)) env) '(if (= 1 2) (= 1 2) (if (= 2 2) (= 2 2) #f)))
  (check-true (eval-scheme '(or (= 1 2) (= 2 2)) env))
  (check-true (= 2 (eval-scheme '(or (= 1 2) 2 (= 2 2)) env)))
  (check-true (= 4 (apply-scheme (eval-scheme '(lambda ((v lazy)) (v)) env) (list 4))))
  ;;Benchmark
  (define-runtime-module-path-index namespace-module '(submod ".." namespace))
  (define-namespace-anchor anchor)
  (define ns (module->namespace namespace-module (namespace-anchor->empty-namespace anchor)))
  (define benchmark1
    '(begin
       (define scheme-traverse
         (time
          (eval-scheme
           '(begin
              (define foldl
                (lambda (proc init list)
                  (if (null? list)
                      init
                      (foldl proc (proc (car list) init) (cdr list)))))
              (define reverse (lambda (l) (foldl cons null l)))
              (define map (lambda (proc l) (reverse (foldl (lambda (e i) (cons (proc e) i)) null l))))
              (lambda (l) (reverse (map add1 l))))
           (make-env (list (cons 'cons (make-primitive cons 2))
                           (cons 'car (make-primitive car 1))
                           (cons 'cdr (make-primitive cdr 1))
                           (cons 'null? (make-primitive null? 1))
                           (cons 'null null)
                           (cons 'add1 (make-primitive add1 1)))))))
       (define racket-traverse
         (time (eval '(lambda (l) (reverse (map add1 l))))))
       (let ((lst (range 0 200000)))
         (check-equal? (time (apply-scheme scheme-traverse (list lst)))
                       (time (apply racket-traverse (list lst)))))))
  (pretty-write benchmark1)
  (eval benchmark1 ns)
  (define benchmark2
    '(begin
       (define scheme-pi-stream-10000th
         (time
          (eval-scheme
           '(begin
              (define foldl
                (lambda (proc init list)
                  (if (null? list)
                      init
                      (foldl proc (proc (car list) init) (cdr list)))))
              (define ormap
                (lambda (proc list)
                  (if (null? list)
                      #t
                      (if (proc (car list)) (ormap proc (cdr list)) #f))))
              (define reverse (lambda (l) (foldl cons null l)))
              (define map (lambda (proc l) (reverse (foldl (lambda (e i) (cons (proc e) i)) null l))))

              (define cons-stream (lambda (car (cdr lazy-memo)) (cons car cdr)))
              (define stream-car (lambda (s) (car s)))
              (define stream-cdr (lambda (s) ((cdr s))))
              (define empty-stream null)
              (define streams-empty?
                (lambda (sl)
                  (ormap null? sl)))
              (define streams-map
                (lambda (proc sl)
                  (if (streams-empty? sl)
                      empty-stream
                      (cons-stream (apply proc (map stream-car sl)) (streams-map proc (map stream-cdr sl))))))
              (define stream-ref
                (lambda (s n)
                  (if (= n 0)
                      (stream-car s)
                      (stream-ref (stream-cdr s) (+ n (- 1))))))

              (define odds/+- (cons-stream 1 (streams-map (lambda (n) (if (< n 0) (+ (- n) 2) (- (+ n 2)))) (cons odds/+- null))))
              (define pi-stream
                (cons-stream (stream-car odds/+-) (streams-map (lambda (o p) (+ (/ 1 o) p)) (cons (stream-cdr odds/+-) (cons pi-stream null)))))
              (* 4 (stream-ref pi-stream 9999)))
           (make-env (list (cons 'null? (make-primitive null? 1))
                           (cons 'car (make-primitive car 1))
                           (cons 'cdr (make-primitive cdr 1))
                           (cons 'cons (make-primitive cons 2))
                           (cons '< (make-primitive < 2))
                           (cons '= (make-primitive = 2))
                           (cons '/ (make-primitive / 2))
                           (cons '+ (make-primitive + 2))
                           (cons '- (make-primitive - 1))
                           (cons '* (make-primitive * 2))
                           (cons 'null null)
                           (cons 'apply (make-primitive apply-scheme 2)))))))
       (define racket-pi-stream-10000th
         (time
          (eval '(begin
                   (define (stream-map* proc . sl)
                     (if (ormap stream-empty? sl)
                         empty-stream
                         (stream-cons #:eager (apply proc (map stream-first sl))
                                      (apply stream-map* proc (map stream-rest sl)))))
                   (define odds/+- (stream-cons #:eager 1 (stream-map* (lambda (n) (if (< n 0) (+ (- n) 2) (- (+ n 2)))) odds/+-)))
                   (define pi-stream (stream-cons #:eager (stream-first odds/+-) (stream-map* (lambda (o p) (+ (/ 1 o) p)) (stream-rest odds/+-) pi-stream)))
                   (* 4 (stream-ref pi-stream 9999))))))
       (check-true (= racket-pi-stream-10000th scheme-pi-stream-10000th))))
  (pretty-write benchmark2)
  (eval benchmark2 ns))
