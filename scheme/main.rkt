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

(require racket/generic racket/match racket/contract (submod racket/performance-hint begin-encourage-inline) (for-syntax racket/base))
(provide (struct-out exn:fail:scheme)
         (struct-out exn:fail:scheme:syntax)
         (struct-out exn:fail:scheme:syntax:primitive)
         (struct-out exn:fail:scheme:syntax:unbound)
         (struct-out exn:fail:scheme:contract)
         (struct-out exn:fail:scheme:contract:arity)
         (struct-out exn:fail:scheme:contract:applicable)

         (struct-out __void)

         scheme-self-evaluating? scheme-variable? scheme-procedure? scheme-primitive?

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

         make-example-base-environment
         eval-scheme
         expand-scheme
         apply-scheme
         (contract-out
          (make-primitive (-> procedure? exact-nonnegative-integer? any))
          (make-optimal-base-environment (->* () ((listof (cons/c symbol? any/c)) #:expander (-> any/c (-> all-implement/c any) any)) any))
          ))

;;Exceptions
(begin-encourage-inline
  (struct exn:fail:scheme exn:fail ())
  (struct exn:fail:scheme:syntax exn:fail:scheme ())
  (struct exn:fail:scheme:syntax:primitive exn:fail:scheme:syntax ())
  (struct exn:fail:scheme:syntax:unbound exn:fail:scheme:syntax ())
  (struct exn:fail:scheme:contract exn:fail:scheme ())
  (struct exn:fail:scheme:contract:arity exn:fail:scheme:contract ())
  (struct exn:fail:scheme:contract:applicable exn:fail:scheme:contract ())
  )

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
(define-syntax-rule (contract-monitor body ...)
  (with-handlers ((exn:fail:contract? (lambda (e) (raise (exn:fail:scheme:contract (exn-message e) (exn-continuation-marks e))))))
    body ...))

;;Structures
(begin-encourage-inline
  (struct __primitive (proc arity) #:constructor-name make-primitive)
  (struct __closure (env arity args body))
  (struct __operands (num list))
  (struct __void ())
  (struct __expander_box (expression))
  (struct __environment (frames expander))
  (struct __thunk (exp env (arg #:auto) (run? #:auto)) #:mutable #:auto-value #f)
  (struct __undefined ())
  )

;;Constants
(define _void (__void))
(define _undefined (__undefined))

;;Utilities
(begin-encourage-inline
  (define (not-define? f) (or (scheme-self-evaluating? f) (scheme-variable? f) (not (define? f))))
  (define (non-empty-list? l) (and (list? l) (not (null? l))))
  (define (check-primitive-part n v pred) (cond ((pred v) v) (else (raise (exn:fail:scheme:syntax:primitive (format "Malformed ~a: ~s" n v) (current-continuation-marks))))))
  (define (raise-arity args vals) (raise (exn:fail:scheme:contract:arity (format "Arity mismatch:\nexpected: ~a\nactual: ~a" args vals) (current-continuation-marks))))
  (define (filter-split proc lst)
    (define r (foldl (lambda (e p) (if (proc e) (cons (cons e (car p)) (cdr p)) (cons (car p) (cons e (cdr p))))) (cons null null) (reverse lst)))
    (values (car r) (cdr r)))
  )

;;Representation
(begin-encourage-inline
  ;;General predicates
  (define (scheme-self-evaluating? v) (or (number? v) (boolean? v) (bytes? v) (__void? v) (eq? v _undefined)))
  (define (scheme-variable? v) (symbol? v))
  (define (scheme-procedure? v) (or (__primitive? v) (__closure? v) (__thunk? v)))
  (define (scheme-primitive? v) (__primitive? v))
  ;;Default representation
  (define (default-representation? f)
    (non-empty-list? f))
  (define (make-define id val) (list 'define id val))
  (define (make-set! id val) (list 'set! id val))
  (define (make-lambda args body) (cons 'lambda (cons args body)))
  (define (make-begin body) (cons 'begin body))
  (define (make-quote datum) (list 'quote datum))
  (define (make-if test first second) (list 'if test first second))
  (define (make-expression operator operands) (cons operator operands))
  )

;;Basic evironments and environment frames operations
(begin-encourage-inline
  ;;Frames
  (define (make-frame assocs) (make-hasheq assocs))
  (define (set-frame! t id val) (hash-set! t id val) _void)
  (define (refer-frame frame id) (hash-ref frame id _undefined))
  (define (has-id? frame id) (hash-has-key? frame id))
  ;;Environments
  (define (make-env assocs #:expander expander) (__environment (list (make-frame assocs)) expander))
  (define (add-frame env assocs) (struct-copy __environment env (frames (cons (make-frame assocs) (__environment-frames env)))))
  (define (raise-unbound id) (raise (exn:fail:scheme:syntax:unbound (format "~a is not bound" id) (current-continuation-marks))))
  (define (lookup-variable env id)
    (let/cc return
      (for ((t (in-list (__environment-frames env))))
        (define v (refer-frame t id))
        (cond ((not (eq? _undefined v)) (return v))))
      (raise-unbound id)))
  (define (env-expand form env) ((__environment-expander env) form __expander_box))
  (define (define-variable! env id val) (set-frame! (car (__environment-frames env)) id val) _void)
  (define (assign-variable! env id val)
    (let/cc break
      (for ((t (in-list (__environment-frames env))))
        (cond ((has-id? t id) (set-frame! t id val) (break _void))))
      (raise-unbound id)))
  )

;;Data-directed dispatching
;;--------------------------
(begin-encourage-inline
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
                       (define (if-second-branch f) (check-and-extract-form f ((list 'if test first second) second) ((list 'if test first) _void))))))

  ;;Scheme expression
  (define-generics s-exp
    (expression? s-exp)
    (expression-operator s-exp)
    (expression-operands s-exp)
    #:defined-predicate s-exp-implement?
    #:fast-defaults ((default-representation?
                       (define (expression? _) #t) ;;A non-empty list can always be considered as an expression
                       (define (expression-operator l) (car l))
                       (define (expression-operands l) (cdr l)))))
  )

;;Contracts
(define all-implement/c (and/c define-implement?
                               set!-implement?
                               begin-implement?
                               if-implement?
                               quote-implement?
                               lambda-implement?
                               s-exp-implement?))

;;Selectors with result checking
(begin-encourage-inline
  (define (n:define-id f) (check-primitive-part 'identifier (define-id f) scheme-variable?))
  (define (n:define-val f) (check-primitive-part 'value (define-val f) not-define?))
  (define (n:set!-id f) (check-primitive-part 'identifier (set!-id f) scheme-variable?))
  (define (n:set!-val f) (check-primitive-part 'value (set!-val f) not-define?))
  (define (n:begin-body f) (check-primitive-part '|begin body| (begin-body f) non-empty-list?))
  (define (n:lambda-args f) (check-primitive-part 'arguments (lambda-args f) (listof (or/c scheme-variable? (list/c scheme-variable? (or/c 'lazy 'lazy-memo))))))
  (define (n:lambda-body f) (check-primitive-part '|lambda body| (lambda-body f) non-empty-list?))
  (define (n:if-test f) (check-primitive-part 'test (if-test f) not-define?))
  (define (n:if-first f) (check-primitive-part 'then (if-first-branch f) not-define?))
  (define (n:if-second f) (check-primitive-part 'else (if-second-branch f) not-define?))
  (define (n:quote-datum f) (quote-datum f))
  (define (n:expression-operator f) (check-primitive-part 'operator (expression-operator f) not-define?))
  (define (n:expression-operands f) (check-primitive-part 'operands (expression-operands f) (listof not-define?)))
  )
;;--------------------------

;;Arity handling
(begin-encourage-inline
  ;;Arguments
  (define (arguments? v)
    (or (list? v) (__operands? v)))
  (define (get-arguments-num-list o)
    (if (list? o) (values (length o) o) (values (__operands-num o) (__operands-list o))))
  (define (make-operands lst)
    (__operands (length lst) lst))
  (define (map-operands p o)
    (struct-copy __operands o (list (map p (__operands-list o)))))
  ;;Procedures
  (define (make-closure env args body)
    (__closure env (length args) args body))
  (define (get-procedure-arity p)
    (cond ((__primitive? p) (__primitive-arity p))
          ((__closure? p) (__closure-arity p))
          (else 0)))
  )

;;Thunks
;;All operands are delayed by the analyzer, while arg fields are not set
;;They are then passed to apply-scheme, and forced or set in terms of arguments
;;But the evaluator can return thunks as well, in which arg fields are set
;;These thunks are considered as first class values, just like closures and other literal values
;;These values are delayed as constants by apply-scheme if they are treated as lazy arguments
(begin-encourage-inline
  (define (delay-it o e)
    (__thunk o e))
  (define (delay-constant c)
    (define new (delay-it (lambda (_) c) #f))
    (set-__thunk-arg! new (list 'constant 'lazy-memo))
    new)
  (define (thunk-arg-set? thunk) (__thunk-arg thunk))
  (define (actual-value t)
    (define (evaluated-thunk? t) (__thunk-run? t))
    (define (lazy-memo-argument? a) (and (list? a) (eq? (cadr a) 'lazy-memo)))
    ;;Get the result anyway, no matter whether the argument field is set
    (cond ((evaluated-thunk? t) (__thunk-exp t))
          (else (define result ((__thunk-exp t) (__thunk-env t)))
                (cond ((lazy-memo-argument? (__thunk-arg t))
                       ;;Garbage collection
                       (set-__thunk-arg! t #t)
                       (set-__thunk-run?! t #t)
                       (set-__thunk-exp! t result)
                       (set-__thunk-env! t #f)))
                result)))
  (define (force-it v)
    ;;Only thunks without their arg fields set, which are produced by the analyzer, are executed
    (if (and (__thunk? v) (not (thunk-arg-set? v))) (actual-value v) v))
  (define (cons-arg-val argument delayed)
    (define (lazy-argument? a) (and (list? a) (or (eq? (cadr a) 'lazy) (eq? (cadr a) 'lazy-memo))))
    (define (argument-name a) (if (scheme-variable? a) a (car a)))
    (define (add-arg-to-thunk arg thunk)
      ;;Thunks with arg field set are treated as simple constants and delayed again
      (cond
        ((thunk-arg-set? thunk) (delay-constant thunk))
        (else
         (set-__thunk-arg! thunk arg)
         thunk)))
    ;;Argument name-value association
    (cons (argument-name argument)
          (if (lazy-argument? argument)
              (cond ((__thunk? delayed) (add-arg-to-thunk argument delayed))
                    (else (delay-constant delayed)))
              (force-it delayed))))
  )

;;Expansion, evaluation and application
(begin-encourage-inline
  (define-values (expand-scheme eval-scheme apply-scheme make-optimal-base-environment make-example-base-environment)
    (letrec ((expand-primitive-internal-sequence ;;Scan out all internal definitions
              (lambda (l)
                (define (define->set d) (make-set! (define-id d) (define-val d)))
                (define appended (append-primitive-sequence-body l))
                (define-values (defs others) (filter-split (lambda (f) (and (default-representation? f) (define? f))) appended))
                (if (null? defs)
                    appended
                    (list
                     (make-expression (make-lambda
                                       (map define-id defs)
                                       (append (map define->set defs) others))
                                      (map (lambda (_) _undefined) defs))))))
             (append-primitive-sequence-body ;;This function will not append sequences recursively
              (lambda (l)
                (foldl (lambda (i a) (if (and (default-representation? i) (begin? i)) (append (begin-body i) a) (cons i a)))
                       null
                       (reverse l))))
             (plain-expand
              (lambda (f e)
                ;;Expand derived expressions and transform all kinds of representations into the default representation
                (cond ((let ((expanded (env-expand f e)))
                         (if (__expander_box? expanded)
                             expanded
                             #f))
                       =>
                       ;;You have to handle identifiers yourself
                       (lambda (b) (plain-expand (__expander_box-expression b) e)))
                      ((or (scheme-variable? f) (scheme-self-evaluating? f)) f)
                      ((if? f) (make-if (plain-expand (n:if-test f) e)
                                        (plain-expand (n:if-first f) e)
                                        (plain-expand (n:if-second f) e)))
                      ((define? f) (make-define (n:define-id f)
                                                (plain-expand (n:define-val f) e)))
                      ((set!? f) (make-set! (n:set!-id f) (plain-expand (n:set!-val f) e)))
                      ((begin? f) (make-begin (append-primitive-sequence-body (map (lambda (f) (plain-expand f e)) (n:begin-body f)))))
                      ((lambda? f) (make-lambda (n:lambda-args f)
                                                (expand-primitive-internal-sequence (map (lambda (f) (plain-expand f e)) (n:lambda-body f)))))
                      ((quote? f) f)
                      ((expression? f) (make-expression (plain-expand (n:expression-operator f) e)
                                                        (map (lambda (f) (plain-expand f e)) (n:expression-operands f))))
                      (else (raise (exn:fail:scheme:syntax (format "Malformed form: ~s" f) (current-continuation-marks)))))))
             (expand-scheme
              (lambda (f e)
                ;;Checking
                (cond ((not (__environment? e)) (raise (exn:fail:scheme:contract (format "~s is not an environment value" e) (current-continuation-marks)))))
                ;;Expansion
                (plain-expand f e)))

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
                      ((scheme-variable? exp) (lambda (env) (lookup-variable env exp)))

                      ((if? exp)
                       (define test (analyze-primitive-form (if-test exp)))
                       (define then (analyze-primitive-form (if-first-branch exp)))
                       (define alter (analyze-primitive-form (if-second-branch exp)))
                       (lambda (env)
                         (if (test env)
                             (then env)
                             (alter env))))
                      ((quote? exp)
                       (define datum (quote-datum exp))
                       (lambda (_) datum))
                      ((begin? exp)
                       (define seq (begin-body exp))
                       (analyze-sequence seq))
                      ((lambda? exp)
                       (define args (lambda-args exp))
                       (define body (analyze-sequence (lambda-body exp)))
                       (lambda (env)
                         (make-closure env args body)))
                      ((set!? exp)
                       (define id (set!-id exp))
                       (define val (analyze-primitive-form (set!-val exp)))
                       (lambda (env) (assign-variable! env id (val env))))
                      ((define? exp)
                       (define id (define-id exp))
                       (define val (analyze-primitive-form (define-val exp)))
                       (lambda (env)
                         (define-variable! env id (val env))))

                      ((expression? exp)
                       (define operator (analyze-primitive-form (expression-operator exp)))
                       (define operands (make-operands (map analyze-primitive-form (expression-operands exp))))
                       (lambda (env)
                         (plain-apply (operator env) (map-operands (lambda (o) (delay-it o env)) operands))))

                      (else (raise (exn:fail:scheme:syntax (format "Malformed form: ~s" exp)) (current-continuation-marks))))))

             (eval-primitive-form (lambda (exp env) ((analyze-primitive-form exp) env)))
             (plain-eval (lambda (exp env) (eval-primitive-form (expand-scheme exp env) env)))

             (plain-apply
              (lambda (operator operands)
                ;;Checking
                (define-values (operands-num operands-list)
                  (cond ((arguments? operands) (get-arguments-num-list operands))
                        (else (raise (exn:fail:scheme:contract (format "~s cannot be supplied as by-position arguments" operands) (current-continuation-marks))))))
                (cond ((not (scheme-procedure? operator))
                       (raise (exn:fail:scheme:contract:applicable (format "~s is not an applicable object" operator) (current-continuation-marks))))
                      ((not (= (get-procedure-arity operator) operands-num))
                       (raise-arity (get-procedure-arity operator) operands-num)))
                (cond ((not (or (__operands? operands) (list? operands)))))
                ;;Application
                (cond ((__primitive? operator)
                       (apply (__primitive-proc operator) (map force-it operands-list)))
                      ((__thunk? operator) (actual-value operator)) ;;These thunks always have their arg fields set
                      (else
                       (define env (add-frame (__closure-env operator) (map cons-arg-val (__closure-args operator) operands-list)))
                       ((__closure-body operator) env)))))

             ;;Exported environment constructors
             (fixed-bindings
              (list
               (cons 'primitive? (make-primitive scheme-primitive? 1))
               (cons 'procedure? (make-primitive scheme-procedure? 1))
               (cons 'self-evaluating? (make-primitive scheme-self-evaluating? 1))
               (cons 'apply (make-primitive plain-apply 2))
               (cons 'eval (make-primitive plain-eval 2))
               (cons 'expand (make-primitive expand-scheme 2))))
             (make-optimal-base-environment
              (lambda ((assoc null) #:expander (expander (lambda _ #f)))
                (define new
                  (make-env
                   #:expander expander
                   (cons (cons 'make-base-environment (make-primitive (lambda () (make-optimal-base-environment assoc #:expander expander)) 0))
                         (cons (cons 'current-environment (make-primitive (lambda () new) 0))
                               (append fixed-bindings assoc)))))
                new))
             (more-fixed-bindings
              (list (cons '+ (make-primitive + 2))
                    (cons '- (make-primitive - 2))
                    (cons '* (make-primitive * 2))
                    (cons '/ (make-primitive / 2))
                    (cons 'number? (make-primitive number? 1))
                    (cons 'real? (make-primitive real? 1))
                    (cons 'rational? (make-primitive rational? 1))
                    (cons 'integer? (make-primitive integer? 1))
                    (cons '< (make-primitive < 2))
                    (cons '> (make-primitive > 2))
                    (cons '= (make-primitive = 2))
                    (cons '<= (make-primitive <= 2))
                    (cons '>= (make-primitive >= 2))
                    (cons 'eq? (make-primitive eq? 2))
                    (cons 'car (make-primitive car 1))
                    (cons 'cdr (make-primitive cdr 1))
                    (cons 'cons (make-primitive cons 2))
                    (cons 'null null)
                    (cons 'null? (make-primitive null? 1))
                    (cons 'list? (make-primitive list? 1))
                    (cons 'bytes? (make-primitive bytes? 1))
                    (cons 'list->bytes (make-primitive list->bytes 1))
                    (cons 'bytes->list (make-primitive bytes->list 1))
                    (cons 'bytes=? (make-primitive bytes=? 2))
                    (cons 'bytes>? (make-primitive bytes>? 2))
                    (cons 'bytes<? (make-primitive bytes<? 2))
                    (cons 'bytes-ref (make-primitive bytes-ref 2))
                    ;;Renamed
                    (cons 'void (make-primitive __void 0))
                    (cons 'void? (make-primitive __void? 1))
                    ))
             (example-expander ;;Works only when the default representation is used
              (lambda (exp c)
                (define (make-let assoc body)
                  (cons 'let (cons assoc body)))
                (match exp
                  ((list 'let (list (list id expr) ...) body ...)
                   (c (make-expression (make-lambda id body) expr)))
                  ((list 'let* (list assoc ...) body ...)
                   (c (car (foldl (lambda (a b) (list (make-let (list a) b))) body (reverse assoc)))))
                  ((list 'letrec (list (list id expr) ...) body ...)
                   (c (make-let null (cons (make-begin (map (lambda (i e) (make-define i e)) id expr)) body))))
                  ((list 'define (cons name args) body ...)
                   (c (make-define name (make-lambda args body))))
                  ((list 'cond (list test body ...) ... (list 'else else-body ...))
                   (c (foldl (lambda (t b e) (make-if t (make-begin b) e))
                             (make-begin else-body)
                             (reverse test)
                             (reverse body))))
                  ((list 'cond (list test body ...) ...)
                   (c (foldl (lambda (t b e) (make-if t (make-begin b) e))
                             _void
                             (reverse test)
                             (reverse body))))
                  (_ #f))))
             (make-example-base-environment
              (lambda ()
                (define new (make-optimal-base-environment more-fixed-bindings #:expander example-expander))
                (plain-eval
                 '(begin
                    (define (cons-stream car (cdr lazy-memo)) (cons car cdr))
                    (define (stream-cdr s) ((cdr s)))
                    (define (stream-car s) (car s))
                    (define stream-empty? null?)
                    (define empty-stream null)

                    (define (add1 n) (+ n 1))
                    (define (sub1 n) (- n 1))
                    (define (minus n) (- 0 n))

                    (define (foldl proc init list)
                      (if (null? list)
                          init
                          (foldl proc (proc (car list) init) (cdr list))))
                    (define (ormap proc list)
                      (if (null? list)
                          #t
                          (if (proc (car list)) (ormap proc (cdr list)) #f)))
                    (define (reverse l) (foldl cons null l))
                    (define (map proc l) (reverse (foldl (lambda (e i) (cons (proc e) i)) null l)))
                    )
                 new)
                new)))
      (values expand-scheme
              (lambda (exp env)
                (contract-monitor (plain-eval exp env)))
              (lambda (operator operands)
                (contract-monitor (plain-apply operator operands)))
              make-optimal-base-environment
              make-example-base-environment)))
  )

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
  (check-not-exn (lambda () (expand-scheme (list (list 1)) (make-optimal-base-environment))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (n:set!-id (default:make-set! '(+ 1 2) 3))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (n:lambda-args (default:make-lambda '(+ 1) '((+ 1 2))))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (n:begin-body (default:make-begin null))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (n:define-val (default:make-define 'a (default:make-define 'b 1)))))
  (check-exn exn:fail:scheme:syntax:unbound? (lambda () (eval-scheme '(+) (make-optimal-base-environment))))
  (check-exn exn:fail:scheme:contract:applicable? (lambda () (eval-scheme '(+) (make-optimal-base-environment (list (cons '+ 0))))))
  (check-exn exn:fail:scheme:contract:arity? (lambda () (eval-scheme '((lambda (n) (+ n 1))) (make-optimal-base-environment (list (cons '+ (make-primitive + 2)))))))
  (check-exn exn:fail:scheme:contract? (lambda () (eval-scheme '(+ "") (make-optimal-base-environment (list (cons '+ (make-primitive + 1)))))))
  (check-exn exn:fail:scheme:contract? (lambda () (eval-scheme '(+ 1 2) null)))
  (check-exn exn:fail:scheme:contract? (lambda () (expand-scheme '(+ 1 2) null)))
  (check-exn exn:fail:scheme:contract? (lambda () (apply-scheme (eval-scheme '(lambda () 1) (make-example-base-environment)) (vector))))
  ;;Selectors
  (check-eq? (n:define-id (default:make-define 'a 1)) 'a)
  (check-equal? (n:if-test (default:make-if '(+ 1 2) 1 2)) '(+ 1 2))
  (check-equal? (n:quote-datum (default:make-quote '(1 . 2))) '(1 . 2))
  ;;Expansion, evaluation and application
  (define env (make-example-base-environment))
  (check-true (= (eval-scheme '(apply + (map (lambda (v) (* v (+ v -1))) '(1 2))) env) 2))
  (check-true (= (apply-scheme (eval-scheme '(lambda (a) (set! a 1) a) env) (list 0)) 1))
  (check-equal? (expand-scheme '(let ((a 1)) (+ a 1)) env) '((lambda (a) (+ a 1)) 1))
  (check-equal? (expand-scheme '(let* ((a 1) (b (+ a 1))) (+ a b)) env) '((lambda (a) ((lambda (b) (+ a b)) (+ a 1))) 1))
  (check-true (= 4 (apply-scheme (eval-scheme '(lambda ((v lazy)) (v)) env) (list 4))))
  (check-equal? (eval-scheme '(eval '(map (lambda (n) (+ n 1)) '(1 2)) (current-environment)) env) '(2 3))
  (check-true (= (eval-scheme '(eval '((lambda (n) (+ n 1)) 1) (make-base-environment)) env) 2))
  (check-true (= (eval-scheme '(begin (define (add1 n) (+ n 1)) (add1 1)) env) 2))
  (check-true (= (eval-scheme '(begin (begin (define a 1)) a) env) 1))
  (check-true (= (eval-scheme '(begin (begin (define b 1)) (define c 2) (begin (+ b c))) env) 3))
  ;;Benchmark
  (define-runtime-module-path-index namespace-module '(submod ".." namespace))
  (define-namespace-anchor anchor)
  (define ns (module->namespace namespace-module (namespace-anchor->empty-namespace anchor)))
  (define benchmark1
    '(begin
       (define scheme-traverse
         (time
          (eval-scheme
           '(lambda (l) (reverse (map add1 l)))
           (make-example-base-environment))))
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
              (define streams-empty?
                (lambda (sl)
                  (ormap stream-empty? sl)))
              (define streams-map
                (lambda (proc sl)
                  (if (streams-empty? sl)
                      empty-stream
                      (cons-stream (apply proc (map stream-car sl)) (streams-map proc (map stream-cdr sl))))))
              (define stream-ref
                (lambda (s n)
                  (if (= n 0)
                      (stream-car s)
                      (stream-ref (stream-cdr s) (sub1 n)))))

              (define odds/+- (cons-stream 1 (streams-map (lambda (n) (if (< n 0) (+ (minus n) 2) (minus (+ n 2)))) (cons odds/+- null))))
              (define pi-stream
                (cons-stream (stream-car odds/+-) (streams-map (lambda (o p) (+ (/ 1 o) p)) (cons (stream-cdr odds/+-) (cons pi-stream null)))))
              (* 4 (stream-ref pi-stream 9999)))
           (make-example-base-environment))))
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
