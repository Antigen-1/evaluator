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

         scheme-self-evaluating? scheme-variable? scheme-primitive? scheme-procedure?

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
          (make-env (->* ((listof (cons/c symbol? any/c))) (#:expander (-> any/c (-> all-implement/c any) any)) env?))
          (eval-scheme (->
                        all-implement/c
                        env?
                        any))
          (apply-scheme (-> any/c list? any))))

;;Exceptions
(struct exn:fail:scheme exn:fail ())
(struct exn:fail:scheme:syntax exn:fail:scheme ())
(struct exn:fail:scheme:syntax:unbound exn:fail:scheme:syntax ())
(struct exn:fail:scheme:application exn:fail:scheme ())

;;Macros
(define-syntax (check-and-extract-form stx)
  (syntax-case stx ()
    ((_ val pattern id)
     #'(match val
         (pattern id)
         (_ (raise (exn:fail:scheme:syntax (format "Malformed scheme form: ~s" val) (current-continuation-marks))))))))

;;Structures
(struct __closure (env args body))
(struct __void ())
(struct __expander_box (expression))

;;Constants
(define _void (__void))

;;Utilities
(define (not-define? f) (not (define? f)))
(define (last-expr? lst)
  ;;Ensure that the last form is not a define form
  (match lst
    ((list _ ... last) #:when (not-define? last) #t)
    (_ #f)))
(define (non-empty-list? l) (and (list? l) (not (null? l))))

;;Representation
;;General predicates
(define (scheme-self-evaluating? v) (or (exact-integer? v) (boolean? v) (bytes? v) (__void? v)))
(define (scheme-variable? v) (symbol? v))
(define (scheme-primitive? v) (or (scheme-self-evaluating? v) (scheme-variable? v)))
(define (scheme-procedure? v) (or (procedure? v) (__closure? v)))
;;Default representation
(define (default-representation? f)
  (or (scheme-primitive? f) (null? f) (and (pair? f) (default-representation? (car f)) (default-representation? (cdr f)))))
(define (make-define id val) (list 'define id val))
(define (make-set! id val) (list 'set! id val))
(define (make-lambda args body) (cons 'lambda (cons args body)))
(define (make-begin body) (cons 'begin body))
(define (make-quote datum) (list 'quote datum))
(define (make-if test first second) (list 'if test first second))
(define (make-expression operator operand) (cons operator operand))

;;Environments
(struct environment (frames expander))
(define (make-env (assocs null) #:expander (expander (lambda _ #f))) (environment (list (make-hasheq assocs)) expander))
(define (add-frame env assocs) (struct-copy environment env (frames (cons (make-hasheq assocs) (environment-frames env)))))
(define (refer-env env id #:proc (proc hash-ref))
  (let/cc return
    (for ((t (in-list (environment-frames env))))
      (cond ((hash-has-key? t id) (return (proc t id)))))
    (raise (exn:fail:scheme:syntax:unbound (format "~a is not bound" id) (current-continuation-marks)))))
(define (expand form env) ((environment-expander env) form __expander_box))
(define ((make-tbl-setter val) t id) (hash-set! t id val) _void)
(define (set-env env id val) (hash-set! (car (environment-frames env)) id val) _void)

;;Special forms
;;Only syntax are checked here
(define forms '(define set! lambda begin quote if))
(define-generics define-form
  (define? define-form)
  (define-id define-form)
  (define-val define-form)
  #:defined-predicate define-implement?
  #:fast-defaults ((default-representation?
                     (define (define? l) (and (non-empty-list? l) (eq? 'define (car l))))
                     (define (define-id f) (check-and-extract-form f (list 'define id _) id))
                     (define (define-val f) (check-and-extract-form f (list 'define _ val) val)))))
(define-generics set!-form
  (set!? set!-form)
  (set!-id set!-form)
  (set!-val set!-form)
  #:defined-predicate set!-implement?
  #:fast-defaults ((default-representation?
                     (define (set!? l) (and (non-empty-list? l) (eq? 'set! (car l))))
                     (define (set!-id f) (check-and-extract-form f (list 'set! id _) id))
                     (define (set!-val f) (check-and-extract-form f (list 'set! _ val) val)))))
(define-generics lambda-form
  (lambda? lambda-form)
  (lambda-args lambda-form)
  (lambda-body lambda-form)
  #:defined-predicate lambda-implement?
  #:fast-defaults ((default-representation?
                     (define (lambda? l) (and (non-empty-list? l) (eq? 'lambda (car l))))
                     (define (lambda-args f) (check-and-extract-form f (list 'lambda (list args ...) _ ...) args))
                     (define (lambda-body f) (check-and-extract-form f (list 'lambda (list _ ...) body ...) body)))))
(define-generics begin-form
  (begin? begin-form)
  (begin-body begin-form)
  #:defined-predicate begin-implement?
  #:fast-defaults ((default-representation?
                     (define (begin? l) (and (non-empty-list? l) (eq? 'begin (car l))))
                     (define (begin-body f) (check-and-extract-form f (list 'begin body ...) body)))))
(define-generics quote-form
  (quote? quote-form)
  (quote-datum quote-form)
  #:defined-predicate quote-implement?
  #:fast-defaults ((default-representation?
                     (define (quote? l) (and (non-empty-list? l) (eq? 'quote (car l))))
                     (define (quote-datum f) (check-and-extract-form f (list 'quote datum) datum)))))
(define-generics if-form
  (if? if-form)
  (if-test if-form)
  (if-first-branch if-form)
  (if-second-branch if-form)
  #:defined-predicate if-implement?
  #:fast-defaults ((default-representation?
                     (define (if? l) (and (non-empty-list? l) (eq? 'if (car l))))
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
                     (define (expression? l) (and (non-empty-list? l) (not (ormap (lambda (h) (eq? h (car l))) forms))))
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
(define (check-result v pred) (cond ((pred v) v) (else (raise (exn:fail:scheme:syntax (format "Malformed scheme form: ~s" v) (current-continuation-marks))))))
(define (n:define-id f) (check-result (define-id f) scheme-variable?))
(define (n:define-val f) (check-result (define-val f) not-define?))
(define (n:set!-id f) (check-result (set!-id f) scheme-variable?))
(define (n:set!-val f) (check-result (set!-val f) not-define?))
(define (n:begin-body f) (check-result (begin-body f) last-expr?))
(define (n:lambda-args f) (check-result (lambda-args f) (listof scheme-variable?)))
(define (n:lambda-body f) (check-result (lambda-body f) last-expr?))
(define (n:if-test f) (check-result (if-test f) not-define?))
(define (n:if-first f) (check-result (if-first-branch f) not-define?))
(define (n:if-second f) (check-result (if-second-branch f) not-define?))
(define (n:quote-datum f) (quote-datum f))
(define (n:expression-operator f) (expression-operator f))
(define (n:expression-operand f) (expression-operand f))

;;Expansion, evaluator and application
(define-values (eval-scheme apply-scheme)
  (letrec ((eval-scheme
            (lambda (exp env)
              (cond ((scheme-self-evaluating? exp) exp)
                    ((let ((expanded (expand exp env)))
                       (if (__expander_box? expanded)
                           expanded
                           #f))
                     =>
                     (lambda (e) (eval-scheme (__expander_box-expression e) env)))
                    ((scheme-variable? exp) (refer-env env exp))
                    ((if? exp)
                     (if (eval-scheme (n:if-test exp) env)
                         (eval-scheme (n:if-first exp) env)
                         (eval-scheme (n:if-second exp) env)))
                    ((quote? exp) (n:quote-datum exp))
                    ((begin? exp) (for/fold ((_ _void)) ((e (in-list (n:begin-body exp)))) (eval-scheme e env)))
                    ((lambda? exp) (__closure env (n:lambda-args exp) (n:lambda-body exp)))
                    ((set!? exp)
                     (refer-env env (n:set!-id exp) #:proc (make-tbl-setter (eval-scheme (n:set!-val exp) env))))
                    ((define? exp)
                     (set-env env (n:define-id exp) (eval-scheme (n:define-val exp) env)))
                    ((expression? exp) (apply-scheme (eval-scheme (n:expression-operator exp) env)
                                                     (map (lambda (e) (eval-scheme e env)) (n:expression-operand exp))))
                    (else (raise (exn:fail:scheme:syntax (format "Malformed scheme expression: ~s" exp)) (current-continuation-marks))))))
           (apply-scheme
            (lambda (operator operand)
              (cond ((procedure? operator) (apply operator operand))
                    ((__closure? operator)
                     (define env (add-frame (__closure-env operator) (map cons (__closure-args operator) operand)))
                     (for/fold ((_ _void))
                               ((ins (in-list (__closure-body operator))))
                       (eval-scheme ins env)))
                    (else (raise (exn:fail:scheme:application (format "~s is not an applicable object" operator) (current-continuation-marks))))))))
    (values eval-scheme apply-scheme)))

(module+ test
  ;; Any code in this `test` submodule runs when this file is run using DrRacket
  ;; or with `raco test`. The code here does not run when this file is
  ;; required by another module.

  (require racket/list rackunit (submod ".."))

  ;;Predicates
  (check-true (default-representation? (default:make-expression '+ '(1 2))))
  (check-false (default-representation? 1.2))
  (check-true (scheme-primitive? #"a"))
  (check-true (scheme-procedure? +))
  (check-true (expression? (default:make-expression '+ '(2 2))))
  ;;Exceptions
  (check-exn exn:fail:scheme:syntax? (lambda () (n:set!-id (default:make-set! '(+ 1 2) 3))))
  (check-exn exn:fail:scheme:syntax? (lambda () (n:begin-body (default:make-begin '((+ 1 2) (define a 1))))))
  (check-exn exn:fail:scheme:syntax? (lambda () (n:lambda-args (default:make-lambda '(+ 1) '((+ 1 2))))))
  (check-exn exn:fail:scheme:syntax:unbound? (lambda () (eval-scheme '(+) (make-env null))))
  (check-exn exn:fail:scheme:application? (lambda () (eval-scheme '(+) (make-env (list (cons '+ 0))))))
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
  (define namespace (make-env (list
                               (cons '+ +)
                               (cons '- -)
                               (cons '* *)
                               (cons '/ /)
                               (cons '= =)
                               (cons 'car car)
                               (cons 'cdr cdr)
                               (cons 'cons cons)
                               (cons 'list list)
                               (cons 'null null)
                               (cons 'null? null?)
                               (cons 'eval eval-scheme)
                               (cons 'apply apply-scheme))
                              #:expander or-matcher))
  (check-true
   (=
    (time
     (eval-scheme
      '(begin
         (define map (lambda (proc l)
                       (if (null? l)
                           '()
                           (cons (proc (car l)) (map proc (cdr l))))))
         (apply + (map (lambda (v) (* v (+ v -1))) (list 1 2))))
      namespace))
    2))
  (check-true (= (apply-scheme (eval-scheme '(lambda (a) (set! a 1) a) namespace) (list 0)) 1))
  (check-true (eval-scheme '(or (= 1 2) (= 2 2)) namespace))
  (check-true (= 2 (eval-scheme '(or (= 1 2) 2 (= 2 2)) namespace))))
