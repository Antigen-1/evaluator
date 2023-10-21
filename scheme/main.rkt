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
         (struct-out exn:fail:scheme:syntax:unbound)
         (struct-out exn:fail:scheme:application)
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
(struct exn:fail:scheme:syntax:unbound exn:fail:scheme:syntax ())
(struct exn:fail:scheme:application exn:fail:scheme ())
(struct exn:fail:scheme:application:arity exn:fail:scheme:application ())

;;Macros
(define-syntax (check-and-extract-form stx)
  (syntax-case stx ()
    ((_ val pattern id)
     #'(match val
         (pattern id)
         (_ (raise (exn:fail:scheme:syntax (format "Malformed scheme form: ~s" val) (current-continuation-marks))))))))

;;Structures
(struct __primitive (proc arity) #:property prop:procedure (struct-field-index proc) #:constructor-name make-primitive)
(struct __closure (env args body))
(struct __void ())
(struct __expander_box (expression))

;;Constants
(define _void (__void))

;;Utilities
(define (non-empty-list? l) (and (list? l) (not (null? l))))
(define (check-result v pred) (cond ((pred v) v) (else (raise (exn:fail:scheme:syntax (format "Malformed scheme form: ~s" v) (current-continuation-marks))))))
(define (raise-arity args vals) (raise (exn:fail:scheme:application:arity (format "Arity mismatch:\nexpected: ~s\nactual: ~s" args vals) (current-continuation-marks))))
(define (map* proc #:handler handler . ll)
  (cond ((apply = (map length ll)) (apply map proc ll))
        (else (handler))))

;;Representation
;;General predicates
(define (scheme-self-evaluating? v) (or (number? v) (boolean? v) (bytes? v) (__void? v)))
(define (scheme-variable? v) (symbol? v))
(define (scheme-procedure? v) (or (__primitive? v) (__closure? v)))
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
(struct environment (frames expander))
(define (make-env (assocs null) #:expander (expander (lambda _ #f))) (environment (list (make-frame assocs)) expander))
(define (add-frame env assocs) (struct-copy environment env (frames (cons (make-frame assocs) (environment-frames env)))))
(define (refer-env env id #:proc (proc refer-frame))
  (let/cc return
    (for ((t (in-list (environment-frames env))))
      (cond ((has-id? t id) (return (proc t id)))))
    (raise (exn:fail:scheme:syntax:unbound (format "~a is not bound" id) (current-continuation-marks)))))
(define (env-expand form env) ((environment-expander env) form __expander_box))
(define (set-env! env id val) (set-frame! (car (environment-frames env)) id val) _void)

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
                     (define (if-second-branch f) (check-and-extract-form f (list 'if test first second) second)))))

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
(define (n:define-id f) (check-result (define-id f) scheme-variable?))
(define (n:define-val f) (define-val f))
(define (n:set!-id f) (check-result (set!-id f) scheme-variable?))
(define (n:set!-val f) (set!-val f))
(define (n:begin-body f) (check-result (begin-body f) list?))
(define (n:lambda-args f) (check-result (lambda-args f) (listof scheme-variable?)))
(define (n:lambda-body f) (check-result (lambda-body f) list?))
(define (n:if-test f) (if-test f))
(define (n:if-first f) (if-first-branch f))
(define (n:if-second f) (if-second-branch f))
(define (n:quote-datum f) (quote-datum f))
(define (n:expression-operator f) (expression-operator f))
(define (n:expression-operand f) (check-result (expression-operand f) list?))
;;--------------------------

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
                     __expander_box-expression)
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
                    (else (raise (exn:fail:scheme:syntax (format "Malformed scheme form: ~s" f) (current-continuation-marks)))))))
           (eval-primitive-form
            (lambda (exp env)
              (cond ((scheme-self-evaluating? exp) exp)
                    ((scheme-variable? exp) (refer-env env exp))

                    ((if? exp)
                     (if (eval-primitive-form (n:if-test exp) env)
                         (eval-primitive-form (n:if-first exp) env)
                         (eval-primitive-form (n:if-second exp) env)))
                    ((quote? exp) (n:quote-datum exp))
                    ((begin? exp) (for/fold ((_ _void)) ((e (in-list (n:begin-body exp)))) (eval-primitive-form e env)))
                    ((lambda? exp) (__closure env (n:lambda-args exp) (n:lambda-body exp)))
                    ((set!? exp)
                     (refer-env env (n:set!-id exp) #:proc (make-frame-setter (eval-primitive-form (n:set!-val exp) env))))
                    ((define? exp)
                     (set-env! env (n:define-id exp) (eval-primitive-form (n:define-val exp) env)))

                    ((expression? exp) (apply-scheme (eval-primitive-form (n:expression-operator exp) env)
                                                     (map (lambda (e) (eval-primitive-form e env)) (n:expression-operand exp))))

                    (else (raise (exn:fail:scheme:syntax (format "Malformed scheme expression: ~s" exp)) (current-continuation-marks))))))
           (apply-scheme
            (lambda (operator operand)
              (cond ((__primitive? operator)
                     (cond ((= (length operand) (__primitive-arity operator))
                            (apply operator operand))
                           (else (raise-arity (__primitive-arity operator) (length operand)))))
                    ((__closure? operator)
                     (define env (add-frame (__closure-env operator) (map* cons #:handler (lambda () (raise-arity (length (__closure-args operator)) (length operand))) (__closure-args operator) operand)))
                     (for/fold ((_ _void))
                               ((ins (in-list (__closure-body operator))))
                       (eval-primitive-form ins env)))
                    (else (raise (exn:fail:scheme:application (format "~s is not an applicable object" operator) (current-continuation-marks))))))))
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
  (check-exn exn:fail:scheme:syntax? (lambda () (n:set!-id (default:make-set! '(+ 1 2) 3))))
  #;(check-exn exn:fail:scheme:syntax? (lambda () (n:begin-body (default:make-begin '((+ 1 2) (define a 1))))))
  (check-exn exn:fail:scheme:syntax? (lambda () (n:lambda-args (default:make-lambda '(+ 1) '((+ 1 2))))))
  (check-exn exn:fail:scheme:syntax:unbound? (lambda () (eval-scheme '(+) (make-env null))))
  (check-exn exn:fail:scheme:application? (lambda () (eval-scheme '(+) (make-env (list (cons '+ 0))))))
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
       (define scheme-pi-stream-1000th
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
              (* 4 (stream-ref pi-stream 999)))
           (make-env (list (cons 'streams-empty? (make-primitive (lambda (l) (ormap null? l)) 1))
                           (cons 'stream-car (make-primitive car 1))
                           (cons 'stream-cdr (make-primitive (lambda (s) (apply-scheme (cdr s) null)) 1))
                           (cons 'empty-stream null)
                           (cons 'null? (make-primitive null? 1))
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
                           (cons 'apply (make-primitive apply-scheme 2)))
                     #:expander (lambda (f c)
                                  (match f
                                    ((list 'cons-stream car cdr)
                                     (c (default:make-expression
                                          'cons
                                          (list car
                                                (default:make-expression
                                                  (default:make-lambda
                                                    '(proc)
                                                    (list
                                                     (default:make-define 'run? #f)
                                                     (default:make-define 'result #f)
                                                     (default:make-lambda
                                                       '()
                                                       (list
                                                        (default:make-if
                                                          'run?
                                                          'result
                                                          (default:make-expression
                                                            (default:make-lambda '(r) (list (default:make-set! 'result 'r) (default:make-set! 'run? #t) 'r))
                                                            (list (default:make-expression 'proc null))))))))
                                                  (list (default:make-lambda '() (list cdr))))))))
                                    (_ #f)))))))
       (define racket-pi-stream-1000th
         (time
          (eval '(begin
                   (define (stream-map* proc . sl)
                     (if (ormap stream-empty? sl)
                         empty-stream
                         (stream-cons #:eager (apply proc (map stream-first sl))
                                      (apply stream-map* proc (map stream-rest sl)))))
                   (define odds/+- (stream-cons #:eager 1 (stream-map* (lambda (n) (if (< n 0) (+ (- n) 2) (- (+ n 2)))) odds/+-)))
                   (define pi-stream (stream-cons #:eager (stream-first odds/+-) (stream-map* (lambda (o p) (+ (/ 1 o) p)) (stream-rest odds/+-) pi-stream)))
                   (* 4 (stream-ref pi-stream 999))))))
       (check-true (= racket-pi-stream-1000th scheme-pi-stream-1000th))))
  (pretty-write benchmark2)
  (eval benchmark2 ns))
