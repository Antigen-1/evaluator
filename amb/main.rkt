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
         (struct-out exn:fail:scheme:ambiguous)

         (struct-out __void)

         scheme-self-evaluating? scheme-variable? scheme-procedure? scheme-primitive?

         default-representation?
         (rename-out (make-if default:make-if)
                     (make-set! default:make-set!)
                     (make-begin default:make-begin)
                     (make-quote default:make-quote)
                     (make-lambda default:make-lambda)
                     (make-define default:make-define)
                     (make-amb default:make-amb)
                     (make-expression default:make-expression)
                     (define-id unsafe:define-id)
                     (define-val unsafe:define-val)
                     (set!-id unsafe:set!-id)
                     (set!-val unsafe:set!-val)
                     (begin-body unsafe:begin-body)
                     (if-test unsafe:if-test)
                     (if-first-branch unsafe:if-first-branch)
                     (if-second-branch unsafe:if-second-branch)
                     (lambda-args unsafe:lambda-args)
                     (lambda-body unsafe:lambda-body)
                     (quote-datum unsafe:quote-datum)
                     (amb-choices unsafe:amb-choices)
                     (expression-operator unsafe:expression-operator)
                     (expression-operands unsafe:expression-operands)
                     (n:define-id checked:define-id)
                     (n:define-val checked:define-val)
                     (n:set!-id checked:set!-id)
                     (n:set!-val checked:set!-val)
                     (n:begin-body checked:begin-body)
                     (n:if-test checked:if-test)
                     (n:if-first-branch checked:if-first-branch)
                     (n:if-second-branch checked:if-second-branch)
                     (n:lambda-args checked:lambda-args)
                     (n:lambda-body checked:lambda-body)
                     (n:quote-datum checked:quote-datum)
                     (n:amb-choices checked:amb-choices)
                     (n:expression-operator checked:expression-operator)
                     (n:expression-operands checked:expression-operands)
                     )
         define? set!? begin? if? lambda? quote? amb? expression?

         gen:amb-form

         make-example-base-environment
         eval-amb
         expand-amb
         apply-amb
         (contract-out
          (make-primitive (-> procedure? exact-nonnegative-integer? any))
          (make-optimal-base-environment (->* () ((listof (cons/c symbol? any/c)) #:succeed (-> any/c any/c any) #:fail (-> any) #:expander (-> any/c (-> scheme-implement? any) any)) any))
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
  (struct exn:fail:scheme:ambiguous exn:fail:scheme ())
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
  (struct __primitive (proc arity) #:transparent #:constructor-name make-primitive)
  (struct __closure (env arity args body) #:transparent)
  (struct __void ())
  (struct __expander_box (expression))
  (struct __environment (frames expander))
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
  (define (raise-arity op args vals) (raise (exn:fail:scheme:contract:arity (format "~a:\nArity mismatch:\nexpected: ~a\nactual: ~a" op args vals) (current-continuation-marks))))
  (define (filter-split proc lst)
    (define r (foldl (lambda (e p) (if (proc e) (cons (cons e (car p)) (cdr p)) (cons (car p) (cons e (cdr p))))) (cons null null) (reverse lst)))
    (values (car r) (cdr r)))
  )

;;Representation
(begin-encourage-inline
  ;;General predicates
  (define (scheme-self-evaluating? v) (or (number? v) (boolean? v) (bytes? v) (__void? v) (eq? v _undefined)))
  (define (scheme-variable? v) (symbol? v))
  (define (scheme-procedure? v) (or (__primitive? v) (__closure? v)))
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
  (define (make-amb choices) (cons 'amb choices))
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
        (cond ((has-id? t id) (set-frame! t id val) (break (refer-frame t id)))))
      (raise-unbound id)))
  )

;;Data-directed dispatching
;;--------------------------
(begin-encourage-inline
  ;;Special forms
  ;;Only syntax are checked here
  (define-generics amb-form
    (define? amb-form)
    (define-id amb-form)
    (define-val amb-form)

    (set!? amb-form)
    (set!-id amb-form)
    (set!-val amb-form)

    (lambda? amb-form)
    (lambda-args amb-form)
    (lambda-body amb-form)

    (begin? amb-form)
    (begin-body amb-form)

    (quote? amb-form)
    (quote-datum amb-form)

    (if? amb-form)
    (if-test amb-form)
    (if-first-branch amb-form)
    (if-second-branch amb-form)

    (amb? amb-form)
    (amb-choices amb-form)

    (expression? amb-form)
    (expression-operator amb-form)
    (expression-operands amb-form)
    #:defined-predicate scheme-implement?
    #:fast-defaults ((default-representation?
                       (define (define? l) (eq? 'define (car l)))
                       (define (define-id f) (check-and-extract-form f (list 'define id _) id))
                       (define (define-val f) (check-and-extract-form f (list 'define _ val) val))

                       (define (set!? l) (eq? 'set! (car l)))
                       (define (set!-id f) (check-and-extract-form f (list 'set! id _) id))
                       (define (set!-val f) (check-and-extract-form f (list 'set! _ val) val))

                       (define (lambda? l) (eq? 'lambda (car l)))
                       (define (lambda-args f) (check-and-extract-form f (list 'lambda (list args ...) _ ...) args))
                       (define (lambda-body f) (check-and-extract-form f (list 'lambda (list _ ...) body ...) body))

                       (define (begin? l) (eq? 'begin (car l)))
                       (define (begin-body f) (check-and-extract-form f (list 'begin body ...) body))

                       (define (quote? l) (eq? 'quote (car l)))
                       (define (quote-datum f) (check-and-extract-form f (list 'quote datum) datum))

                       (define (if? l) (eq? 'if (car l)))
                       (define (if-test f) (check-and-extract-form f (list 'if test _ ...) test))
                       (define (if-first-branch f) (check-and-extract-form f ((list 'if test first second) first) ((list 'if test first) first)))
                       (define (if-second-branch f) (check-and-extract-form f ((list 'if test first second) second) ((list 'if test first) _void)))

                       (define (amb? l) (eq? 'amb (car l)))
                       (define (amb-choices f) (check-and-extract-form f (cons 'amb choices) choices))

                       (define (expression? _) #t) ;;A non-empty list can always be considered as an expression
                       (define (expression-operator l) (car l))
                       (define (expression-operands l) (cdr l)))))
  )

;;Selectors with result checking
(begin-encourage-inline
  (define (n:define-id f) (check-primitive-part 'identifier (define-id f) scheme-variable?))
  (define (n:define-val f) (check-primitive-part 'value (define-val f) not-define?))
  (define (n:set!-id f) (check-primitive-part 'identifier (set!-id f) scheme-variable?))
  (define (n:set!-val f) (check-primitive-part 'value (set!-val f) not-define?))
  (define (n:begin-body f) (check-primitive-part '|begin body| (begin-body f) non-empty-list?))
  (define (n:lambda-args f) (check-primitive-part 'arguments (lambda-args f) (listof scheme-variable?)))
  (define (n:lambda-body f) (check-primitive-part '|lambda body| (lambda-body f) non-empty-list?))
  (define (n:if-test f) (check-primitive-part 'test (if-test f) not-define?))
  (define (n:if-first-branch f) (check-primitive-part 'then (if-first-branch f) not-define?))
  (define (n:if-second-branch f) (check-primitive-part 'else (if-second-branch f) not-define?))
  (define (n:quote-datum f) (quote-datum f))
  (define (n:amb-choices f) (check-primitive-part '|amb choices| (amb-choices f) (listof not-define?)))
  (define (n:expression-operator f) (check-primitive-part 'operator (expression-operator f) not-define?))
  (define (n:expression-operands f) (check-primitive-part 'operands (expression-operands f) (listof not-define?)))
  )
;;--------------------------

;;Arity handling
(begin-encourage-inline
  ;;Arguments
  (define (arguments? v) (list? v))
  (define (get-arguments-num-list o) (values (length o) o))
  (define (eval-arguments:left->right aprocs env succeed fail)
    (if (null? aprocs)
        (succeed null fail)
        ((car aprocs)
         env
         (lambda (arg fail1)
           (eval-arguments:left->right
            (cdr aprocs)
            env
            (lambda (args fail2)
              (succeed (cons arg args) fail2))
            fail1))
         fail)))
  ;;Procedures
  (define (make-closure env args body)
    (__closure env (length args) args body))
  (define (get-procedure-arity p)
    (cond ((__primitive? p) (__primitive-arity p))
          (else (__closure-arity p))))
  )

;;Expansion, evaluation and application
(begin-encourage-inline
  (define-values (expand-amb eval-amb apply-amb make-optimal-base-environment make-example-base-environment)
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
                                        (plain-expand (n:if-first-branch f) e)
                                        (plain-expand (n:if-second-branch f) e)))
                      ((define? f) (make-define (n:define-id f)
                                                (plain-expand (n:define-val f) e)))
                      ((set!? f) (make-set! (n:set!-id f) (plain-expand (n:set!-val f) e)))
                      ((begin? f) (make-begin (append-primitive-sequence-body (map (lambda (f) (plain-expand f e)) (n:begin-body f)))))
                      ((lambda? f) (make-lambda (n:lambda-args f)
                                                (expand-primitive-internal-sequence (map (lambda (f) (plain-expand f e)) (n:lambda-body f)))))
                      ((quote? f) f)
                      ((amb? f) (make-amb (map (lambda (c) (plain-expand c e)) (n:amb-choices f))))
                      ((expression? f) (make-expression (plain-expand (n:expression-operator f) e)
                                                        (map (lambda (f) (plain-expand f e)) (n:expression-operands f))))
                      (else (raise (exn:fail:scheme:syntax (format "Malformed form: ~s" f) (current-continuation-marks)))))))
             (expand-amb
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
                  (lambda (env succeed fail) (first env (lambda (_ fail1) (then env succeed fail1)) fail)))
                (define (loop first rest)
                  (if (null? rest)
                      first
                      (loop (sequentially first (car rest))
                            (cdr rest))))
                (loop (analyze-primitive-form (car seq)) (map analyze-primitive-form (cdr seq)))))
             (analyze-primitive-form
              (lambda (exp)
                (cond ((scheme-self-evaluating? exp) (lambda (_ succeed fail) (succeed exp fail)))
                      ((scheme-variable? exp) (lambda (env succeed fail) (succeed (lookup-variable env exp) fail)))

                      ((if? exp)
                       (define test-proc (analyze-primitive-form (if-test exp)))
                       (define then-proc (analyze-primitive-form (if-first-branch exp)))
                       (define alter-proc (analyze-primitive-form (if-second-branch exp)))
                       (lambda (env succeed fail)
                         (test-proc
                          env
                          (lambda (test-value fail1)
                            (if test-value
                                (then-proc env succeed fail1)
                                (alter-proc env succeed fail1)))
                          fail)))
                      ((quote? exp)
                       (define datum (quote-datum exp))
                       (lambda (_ succeed fail) (succeed datum fail)))
                      ((begin? exp)
                       (define seq (begin-body exp))
                       (analyze-sequence seq))
                      ((lambda? exp)
                       (define args (lambda-args exp))
                       (define body-proc (analyze-sequence (lambda-body exp)))
                       (lambda (env succeed fail)
                         (succeed (make-closure env args body-proc) fail)))
                      ((set!? exp)
                       (define id (set!-id exp))
                       (define val-proc (analyze-primitive-form (set!-val exp)))
                       (lambda (env succeed fail)
                         (val-proc
                          env
                          (lambda (v fail1)
                            (define old (assign-variable! env id v))
                            (succeed _void (lambda () (assign-variable! env id old) (fail1))))
                          fail)))
                      ((define? exp)
                       (define id (define-id exp))
                       (define val-proc (analyze-primitive-form (define-val exp)))
                       (lambda (env succeed fail)
                         (val-proc
                          env
                          (lambda (v fail1)
                            (succeed (define-variable! env id v) fail1))
                          fail)))
                      ((amb? exp)
                       (define choice-procs (map analyze-primitive-form (amb-choices exp)))
                       (lambda (env succeed fail)
                         (define (try-next choices)
                           (if (null? choices)
                               (fail)
                               ((car choices) env succeed (lambda () (try-next (cdr choices))))))
                         (try-next choice-procs)))

                      ((expression? exp)
                       (define operator-proc (analyze-primitive-form (expression-operator exp)))
                       (define operand-procs (map analyze-primitive-form (expression-operands exp)))
                       (lambda (env succeed fail)
                         (operator-proc
                          env
                          (lambda (proc fail1)
                            (eval-arguments:left->right
                             operand-procs
                             env
                             (lambda (args fail2) (plain-apply proc args succeed fail2))
                             fail1))
                          fail)))

                      (else (raise (exn:fail:scheme:syntax (format "Malformed form: ~s" exp)) (current-continuation-marks))))))

             (eval-primitive-form (lambda (exp env succeed fail) ((analyze-primitive-form exp) env succeed fail)))
             (plain-eval (lambda (exp env succeed fail) (eval-primitive-form (expand-amb exp env) env succeed fail)))

             (plain-apply
              (lambda (operator operands succeed fail)
                ;;Checking
                (define-values (operands-num operands-list)
                  (cond ((arguments? operands) (get-arguments-num-list operands))
                        (else (raise (exn:fail:scheme:contract (format "~s cannot be supplied as by-position arguments" operands) (current-continuation-marks))))))
                (cond ((not (scheme-procedure? operator))
                       (raise (exn:fail:scheme:contract:applicable (format "~s is not an applicable object" operator) (current-continuation-marks))))
                      ((not (= (get-procedure-arity operator) operands-num))
                       (raise-arity operator (get-procedure-arity operator) operands-num)))
                ;;Application
                (cond ((__primitive? operator)
                       (succeed (apply (__primitive-proc operator) operands-list) fail))
                      (else
                       (define env (add-frame (__closure-env operator) (map cons (__closure-args operator) operands-list)))
                       ((__closure-body operator) env succeed fail)))))

             ;;Default success and failure handlers
             (default-succeed (lambda (v _) v))
             (default-fail (lambda () (raise (exn:fail:scheme:ambiguous "There are no more choices" (current-continuation-marks)))))

             ;;Exported environment constructors
             (fixed-bindings
              (list (cons 'expand (make-primitive expand-amb 2))))
             (make-optimal-base-environment
              (lambda ((assoc null) #:succeed (succeed default-succeed) #:fail (fail default-fail) #:expander (expander (lambda _ #f)))
                (define new
                  (make-env
                   #:expander expander
                   (append
                    (list (cons 'apply (make-primitive (lambda (exp env) (plain-apply exp env succeed fail)) 2))
                          (cons 'eval (make-primitive (lambda (exp env) (plain-eval exp env succeed fail)) 2))
                          (cons 'the-global-environment (make-primitive (lambda () new) 0))
                          (cons 'make-base-environment (make-primitive (lambda () (make-example-base-environment #:fail fail #:succeed succeed)) 0)))
                    fixed-bindings
                    assoc)))
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
                    (cons 'not (make-primitive not 1))
                    ;;Renamed
                    (cons 'primitive? (make-primitive scheme-primitive? 1))
                    (cons 'procedure? (make-primitive scheme-procedure? 1))
                    (cons 'self-evaluating? (make-primitive scheme-self-evaluating? 1))
                    (cons 'void (make-primitive __void 0))
                    (cons 'void? (make-primitive __void? 1))
                    ))
             (example-expander ;;Works only when the default representation is used
              (lambda (exp c)
                (define (make-let assoc body)
                  (cons 'let (cons assoc body)))
                (define (make-delay e)
                  (list 'delay e))
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
                  ((list 'delay e)
                   (c
                    (make-let (list (list 'run? #f) (list 'result #f) (list 'thunk (make-lambda null (list e))))
                              (list
                               (make-lambda
                                null
                                (list (make-if 'run?
                                               'result
                                               (make-begin (list (make-define 'temp (make-expression 'thunk null))
                                                                 (make-set! 'result 'temp)
                                                                 (make-set! 'run? #t)
                                                                 (make-set! 'thunk #f)
                                                                 'temp)))))))))
                  ((list 'cons-stream a d)
                   (c (make-let (list (list 'immed a) (list 'promise (make-delay d))) (list (make-lambda '(proc) (list (make-expression 'proc (list 'immed 'promise))))))))
                  ((list 'and branches ...)
                   (c (foldl (lambda (b t) (make-let (list (list 'test b)) (list (make-if 'test t 'test))))
                             'test
                             (reverse branches))))
                  ((list 'or branches)
                   (c (foldl (lambda (b e) (make-let (list (list 'test b)) (list (make-if 'test 'test e))))
                             'test
                             (reverse branches))))
                  (_ #f))))
             (make-example-base-environment
              (lambda (#:fail (fail default-fail) #:succeed (succeed default-succeed))
                (define new
                  (make-optimal-base-environment more-fixed-bindings
                   #:expander example-expander #:succeed succeed #:fail fail))
                (plain-eval
                 '(begin
                    ;;All protected
                    (define require (let ((not not)) (lambda (test) (if (not test) (amb)))))

                    (define (force promise) (promise))
                    (define stream-car (let ((scar (lambda (a d) a))) (lambda (s) (s scar))))
                    (define stream-cdr (let* ((force force) (scdr (lambda (a d) (force d)))) (lambda (s) (s scdr))))
                    (define stream-empty? null?)
                    (define empty-stream null)

                    (define add1 (let ((+ +)) (lambda (n) (+ n 1))))
                    (define sub1 (let ((- -)) (lambda (n) (- n 1))))
                    (define minus (let ((- -)) (lambda (n) (- 0 n))))
                    (define abs (let ((>= >=) (minus minus)) (lambda (n) (if (>= n 0) n (minus n)))))

                    (define foldl
                      (let ((null? null?) (car car) (cdr cdr))
                        (lambda (proc init list)
                          (if (null? list)
                              init
                              (foldl proc (proc (car list) init) (cdr list))))))
                    (define andmap
                      (let ((null? null?) (car car) (cdr cdr))
                        (lambda (proc list)
                          (if (null? list)
                              #t
                              (if (proc (car list)) (andmap proc (cdr list)) #f)))))
                    (define ormap
                      (let ((null? null?) (car car) (cdr cdr))
                        (lambda (proc list)
                          (if (null? list)
                              #f
                              (if (proc (car list)) #t (ormap proc (cdr list)))))))
                    (define reverse (let ((cons cons) (null null) (foldl foldl)) (lambda (l) (foldl cons null l))))
                    (define map (let ((cons cons) (foldl foldl) (null null)) (lambda (proc l) (reverse (foldl (lambda (e i) (cons (proc e) i)) null l)))))
                    (define member (let ((car car) (cdr cdr)) (lambda (val items cpr) (cond ((null? items) #f) ((cpr (car items) val) items) (else (member val (cdr items) cpr))))))
                    )
                 new
                 default-succeed
                 default-fail)
                new)))
      (values expand-amb
              (lambda (exp env (succeed default-succeed) (fail default-fail))
                (contract-monitor (plain-eval exp env succeed fail)))
              (lambda (operator operands (succeed default-succeed) (fail default-fail))
                (contract-monitor (plain-apply operator operands succeed fail)))
              make-optimal-base-environment
              make-example-base-environment)))
  )

(module* namespace racket/base
  (require rackunit racket/list racket/stream racket/match (submod ".."))
  (provide (all-from-out rackunit racket/list racket/stream racket/match racket/base (submod ".."))))

(module* test racket/base
  ;; Any code in this `test` submodule runs when this file is run using DrRacket
  ;; or with `raco test`. The code here does not run when this file is
  ;; required by another module.

  (require racket/runtime-path racket/pretty (submod ".." namespace) (for-syntax racket/base))

  ;;Predicates
  (check-true (default-representation? (default:make-expression '+ '(1 2))))
  (check-true (scheme-self-evaluating? 1.2))
  (check-false (scheme-procedure? +))
  (check-true (scheme-procedure? (make-primitive + 2)))
  (check-true (expression? (default:make-expression '+ '(2 2))))
  ;;Exceptions
  (check-not-exn (lambda () (expand-amb (list (list 1)) (make-optimal-base-environment))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (checked:set!-id (default:make-set! '(+ 1 2) 3))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (checked:lambda-args (default:make-lambda '(+ 1) '((+ 1 2))))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (checked:begin-body (default:make-begin null))))
  (check-exn exn:fail:scheme:syntax:primitive? (lambda () (checked:define-val (default:make-define 'a (default:make-define 'b 1)))))
  (check-exn exn:fail:scheme:syntax:unbound? (lambda () (eval-amb '(+) (make-optimal-base-environment))))
  (check-exn exn:fail:scheme:contract:applicable? (lambda () (eval-amb '(+) (make-optimal-base-environment (list (cons '+ 0))))))
  (check-exn exn:fail:scheme:contract:arity? (lambda () (eval-amb '((lambda (n) (+ n 1))) (make-optimal-base-environment (list (cons '+ (make-primitive + 2)))))))
  (check-exn exn:fail:scheme:contract? (lambda () (eval-amb '(+ "") (make-optimal-base-environment (list (cons '+ (make-primitive + 1)))))))
  (check-exn exn:fail:scheme:contract? (lambda () (eval-amb '(+ 1 2) null)))
  (check-exn exn:fail:scheme:contract? (lambda () (expand-amb '(+ 1 2) null)))
  (check-exn exn:fail:scheme:contract? (lambda () (apply-amb (eval-amb '(lambda () 1) (make-example-base-environment)) (vector))))
  ;;Selectors
  (check-eq? (checked:define-id (default:make-define 'a 1)) 'a)
  (check-equal? (checked:if-test (default:make-if '(+ 1 2) 1 2)) '(+ 1 2))
  (check-equal? (checked:quote-datum (default:make-quote '(1 . 2))) '(1 . 2))
  ;;Expansion, evaluation and application
  (define env (make-example-base-environment))
  (check-true (= (eval-amb '((lambda (n) (cond ((>= n 0) n) (else (minus n)))) -1) env) 1))
  (check-true (= (eval-amb '(apply + (map (lambda (v) (* v (+ v -1))) '(1 2))) env) 2))
  (check-true (= (apply-amb (eval-amb '(lambda (a) (set! a 1) a) env) (list 0)) 1))
  (check-equal? (expand-amb '(let ((a 1)) (+ a 1)) env) '((lambda (a) (+ a 1)) 1))
  (check-equal? (expand-amb '(let* ((a 1) (b (+ a 1))) (+ a b)) env) '((lambda (a) ((lambda (b) (+ a b)) (+ a 1))) 1))
  (check-true (= (eval-amb '(eval '((lambda (n) (+ n 1)) 1) (make-base-environment)) env) 2))
  (check-equal? (eval-amb '(eval '(map (lambda (n) (add1 n)) '(1 2)) (the-global-environment)) env) '(2 3))
  (check-true (= (eval-amb '(begin (define (add1 n) (+ n 1)) (add1 1)) env) 2))
  (check-true (= (eval-amb '(begin (begin (define a 1)) a) env) 1))
  (check-true (= (eval-amb '(begin (begin (define b 1)) (define c 2) (begin (+ b c))) env) 3))
  (check-true (= (eval-amb '(force (delay (+ 1 2))) env) 3))
  (check-true (= (eval-amb '(stream-cdr (cons-stream 1 2)) env) 2))
  ;;Benchmark
  (define-runtime-module-path-index namespace-module '(submod ".." namespace))
  (define-namespace-anchor anchor)
  (define ns (module->namespace namespace-module (namespace-anchor->empty-namespace anchor)))
  (define benchmark1
    '(begin
       (define scheme-traverse
         (time
          (eval-amb
           '(lambda (l) (reverse (map add1 l)))
           (make-example-base-environment))))
       (define racket-traverse
         (time (eval '(lambda (l) (reverse (map add1 l))))))
       (let ((lst (range 0 200000)))
         (check-equal? (time (apply-amb scheme-traverse (list lst)))
                       (time (apply racket-traverse (list lst)))))))
  (pretty-write benchmark1)
  (eval benchmark1 ns)
  (define benchmark2
    '(begin
       (define scheme-pi-stream-10000th
         (time
          (eval-amb
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

              (define odds/+- (cons-stream 1 (streams-map (lambda (n) (if (< n 0) (- 2 n) (minus (+ n 2)))) (cons odds/+- null))))
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
                   (define odds/+- (stream-cons #:eager 1 (stream-map* (lambda (n) (if (< n 0) (- 2 n) (- (+ n 2)))) odds/+-)))
                   (define pi-stream (stream-cons #:eager (stream-first odds/+-) (stream-map* (lambda (o p) (+ (/ 1 o) p)) (stream-rest odds/+-) pi-stream)))
                   (* 4 (stream-ref pi-stream 9999))))))
       (check-true (= racket-pi-stream-10000th scheme-pi-stream-10000th))))
  (pretty-write benchmark2)
  (eval benchmark2 ns)
  (define benchmark3
    '(begin
       (define amb-first-possibility
         (time
          (eval-amb
           '(let ((baker (amb 1 2 3 4 5))
                  (fletcher (amb 1 2 3 4 5))
                  (smith (amb 1 2 3 4 5))
                  (cooper (amb 1 2 3 4 5))
                  (miller (amb 1 2 3 4 5)))
              (define names '(baker fletcher smith cooper miller))
              (define results (cons baker (cons fletcher (cons smith (cons cooper (cons miller null))))))
              (define (distinct? items)
                (cond ((null? items) #t)
                      ((null? (cdr items)) #t)
                      ((member (car items) (cdr items) =) #f)
                      (else (distinct? (cdr items)))))
              (define (map* proc ll)
                (if (ormap null? ll)
                    null
                    (cons (apply proc (map car ll)) (map* proc (map cdr ll)))))
              (require (distinct? results))
              (require (not (= baker 5)))
              (require (not (= cooper 1)))
              (require (and (not (= fletcher 1)) (not (= fletcher 5))))
              (require (> miller cooper))
              (require (not (= (abs (- smith fletcher)) 1)))
              (require (not (= (abs (- fletcher cooper)) 1)))
              (map* cons (cons names (cons results null))))
           (make-example-base-environment))))
       (define racket-first-possibility
         (time
          (eval
           '(let ((baker '(1 2 3 4 5))
                  (fletcher '(1 2 3 4 5))
                  (smith '(1 2 3 4 5))
                  (cooper '(1 2 3 4 5))
                  (miller '(1 2 3 4 5)))
              (define all (cartesian-product baker fletcher smith cooper miller))
              (define (distinct? items)
                (cond ((null? items) #t)
                      ((null? (cdr items)) #t)
                      ((member (car items) (cdr items) =) #f)
                      (else (distinct? (cdr items)))))
              (map
               cons
               '(baker fletcher smith cooper miller)
               (car
                (filter (lambda (p)
                          (match p
                            ((list baker fletcher smith cooper miller)
                             (and (distinct? p)
                                  (not (= baker 5))
                                  (not (= cooper 1))
                                  (not (= fletcher 1))
                                  (not (= fletcher 5))
                                  (> miller cooper)
                                  (not (= 1 (abs (- smith fletcher))))
                                  (not (= 1 (abs (- fletcher cooper))))))))
                        all)))))))
       (check-equal? amb-first-possibility racket-first-possibility)))
  (pretty-write benchmark3)
  (eval benchmark3 ns))
