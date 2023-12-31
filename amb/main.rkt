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

(require racket/generic racket/match racket/contract racket/list (submod racket/performance-hint begin-encourage-inline) (for-syntax racket/base))
(provide (struct-out exn:fail:amb)
         (struct-out exn:fail:amb:syntax)
         (struct-out exn:fail:amb:syntax:primitive)
         (struct-out exn:fail:amb:syntax:unbound)
         (struct-out exn:fail:amb:contract)
         (struct-out exn:fail:amb:contract:arity)
         (struct-out exn:fail:amb:contract:applicable)
         (struct-out exn:fail:amb:ambiguous)

         (struct-out __void)

         amb-self-evaluating? amb-variable? amb-procedure? amb-primitive?

         default-representation?
         (rename-out (make-if default:make-if)
                     (make-set! default:make-set!)
                     (make-begin default:make-begin)
                     (make-quote default:make-quote)
                     (make-lambda-args default:make-lambda-args)
                     (make-lambda default:make-lambda)
                     (make-define default:make-define)
                     (make-amb default:make-amb)
                     (make-catch default:make-catch)
                     (make-expression default:make-expression)
                     (define-id unsafe:define-id)
                     (define-val unsafe:define-val)
                     (set!-id unsafe:set!-id)
                     (set!-val unsafe:set!-val)
                     (begin-body unsafe:begin-body)
                     (if-test unsafe:if-test)
                     (if-first-branch unsafe:if-first-branch)
                     (if-second-branch unsafe:if-second-branch)
                     (lambda-fixed-args unsafe:lambda-fixed-args)
                     (lambda-any-arg unsafe:lambda-any-arg)
                     (lambda-body unsafe:lambda-body)
                     (quote-datum unsafe:quote-datum)
                     (amb-choices unsafe:amb-choices)
                     (catch-body unsafe:catch-body)
                     (catch-else unsafe:catch-else)
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
                     (n:lambda-fixed-args checked:lambda-fixed-args)
                     (n:lambda-any-arg checked:lambda-any-arg)
                     (n:lambda-body checked:lambda-body)
                     (n:quote-datum checked:quote-datum)
                     (n:amb-choices checked:amb-choices)
                     (n:catch-body checked:catch-body)
                     (n:catch-else checked:catch-else)
                     (n:expression-operator checked:expression-operator)
                     (n:expression-operands checked:expression-operands)
                     )
         define? set!? begin? if? lambda? quote? amb? catch? expression?
         permanent-set!? typical-set!? ramb? typical-amb?

         gen:amb-form

         make-example-base-environment
         eval-amb
         expand-amb
         apply-amb
         (contract-out
          (make-optimal-base-environment (->* () ((listof (cons/c symbol? any/c)) #:succeed (-> any/c any/c any) #:fail (-> any) #:expander (-> any/c (-> amb-implement? any) any)) any))
          ))

;;Exceptions
(begin-encourage-inline
  (struct exn:fail:amb exn:fail ())
  (struct exn:fail:amb:syntax exn:fail:amb ())
  (struct exn:fail:amb:syntax:primitive exn:fail:amb:syntax ())
  (struct exn:fail:amb:syntax:unbound exn:fail:amb:syntax ())
  (struct exn:fail:amb:contract exn:fail:amb ())
  (struct exn:fail:amb:contract:arity exn:fail:amb:contract ())
  (struct exn:fail:amb:contract:applicable exn:fail:amb:contract ())
  (struct exn:fail:amb:ambiguous exn:fail:amb ())
  )

;;Macros
(define-syntax (check-and-extract-form stx)
  (syntax-case stx ()
    ((_ val (pattern id) ...)
     #'(match val
         (pattern id)
         ...
         (_ (raise (exn:fail:amb:syntax:primitive (format "Malformed amb form: ~s" val) (current-continuation-marks))))))
    ((_ val pattern id)
     #'(match val
         (pattern id)
         (_ (raise (exn:fail:amb:syntax:primitive (format "Malformed amb form: ~s" val) (current-continuation-marks))))))))
(define-syntax-rule (contract-monitor body ...)
  (with-handlers ((exn:fail:contract? (lambda (e) (raise (exn:fail:amb:contract (exn-message e) (exn-continuation-marks e))))))
    body ...))

;;Structures
(begin-encourage-inline
  (struct __closure (env mask fixed any body) #:transparent)
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
  (define (not-define? f) (or (amb-self-evaluating? f) (amb-variable? f) (not (define? f))))
  (define (non-empty-list? l) (and (list? l) (not (null? l))))
  (define (check-primitive-part n v pred) (cond ((pred v) v) (else (raise (exn:fail:amb:syntax:primitive (format "Malformed ~a: ~s" n v) (current-continuation-marks))))))
  (define (raise-arity op args vals) (raise (exn:fail:amb:contract:arity (format "~a:\nArity mismatch:\narity mask: ~a\nactual number: ~a" op args vals) (current-continuation-marks))))
  (define (filter-split proc lst)
    (define r (foldl (lambda (e p) (if (proc e) (cons (cons e (car p)) (cdr p)) (cons (car p) (cons e (cdr p))))) (cons null null) (reverse lst)))
    (values (car r) (cdr r)))
  )

;;Representation
(begin-encourage-inline
  ;;General predicates
  (define (amb-self-evaluating? v) (or (number? v) (boolean? v) (bytes? v) (__void? v) (eq? v _undefined)))
  (define (amb-variable? v) (symbol? v))
  (define (amb-procedure? v) (or (procedure? v) (__closure? v)))
  (define (amb-primitive? v) (procedure? v))
  ;;Default representation
  (define (default-representation? f)
    (non-empty-list? f))
  (define (make-define id val) (list 'define id val))
  (define (make-set! #:permanent? (permanent? #f) id val) (list (if permanent? 'permanent-set! 'set!) id val))
  (define (make-lambda-args fixed any) (if (null? fixed) any `(,@fixed . ,any))) ;;For backward compatibility
  (define (make-lambda args body) (cons 'lambda (cons args body)))
  (define (make-begin body) (cons 'begin body))
  (define (make-quote datum) (list 'quote datum))
  (define (make-if test first second) (list 'if test first second))
  (define (make-amb #:random? (random? #f) choices) (cons (if random? 'ramb 'amb) choices))
  (define (make-catch body then) (list 'catch body then))
  (define (make-expression operator operands) (cons operator operands))
  )

;;Basic evironments and environment frames operations
(begin-encourage-inline
  ;;Frames
  (define (make-frame assocs) (make-hasheq assocs))
  (define (frame-set! t id val) (hash-set! t id val) _void)
  (define (frame-ref frame id) (hash-ref frame id _undefined))
  (define (frame-has-id? frame id) (hash-has-key? frame id))
  ;;Environments
  (define (make-environment assocs #:expander expander) (__environment (list (make-frame assocs)) expander))
  (define (environment-add-frame env assocs) (struct-copy __environment env (frames (cons (make-frame assocs) (__environment-frames env)))))
  (define (environment-expand form env) ((__environment-expander env) form __expander_box))
  (define (raise-unbound id) (raise (exn:fail:amb:syntax:unbound (format "~a is not bound" id) (current-continuation-marks))))
  (define (environment-lookup-variable env id)
    (let/cc return
      (for ((t (in-list (__environment-frames env))))
        (define v (frame-ref t id))
        (cond ((not (eq? _undefined v)) (return v))))
      (raise-unbound id)))
  (define (environment-define-variable! env id val) (frame-set! (car (__environment-frames env)) id val) _void)
  (define (environment-assign-variable! env id val)
    (let/cc break
      (for ((t (in-list (__environment-frames env))))
        (cond ((frame-has-id? t id) (frame-set! t id val) (break (frame-ref t id)))))
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
    (typical-set!? amb-form)
    (permanent-set!? amb-form)
    (set!-id amb-form)
    (set!-val amb-form)

    (lambda? amb-form)
    (lambda-fixed-args amb-form)
    (lambda-any-arg amb-form)
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
    (typical-amb? amb-form)
    (ramb? amb-form)
    (amb-choices amb-form)

    (catch? amb-form)
    (catch-body amb-form)
    (catch-else amb-form)

    (expression? amb-form)
    (expression-operator amb-form)
    (expression-operands amb-form)
    #:defined-predicate amb-implement?
    #:fast-defaults ((default-representation?
                       (define (tagged-with? sym lst) (eq? sym (car lst)))

                       (define (define? l) (tagged-with? 'define l))
                       (define (define-id f) (check-and-extract-form f `(define ,id ,_) id))
                       (define (define-val f) (check-and-extract-form f `(define ,_ ,val) val))

                       (define (typical-set!? l) (tagged-with? 'set! l))
                       (define (permanent-set!? l) (tagged-with? 'permanent-set! l))
                       (define (set!? l) (or (typical-set!? l) (permanent-set!? l)))
                       (define (set!-id f) (check-and-extract-form f `(,_ ,id ,_) id))
                       (define (set!-val f) (check-and-extract-form f `(,_ ,_ ,val) val))

                       (define (lambda? l) (tagged-with? 'lambda l))
                       (define (lambda-body f) (check-and-extract-form f `(lambda ,_ ,body ...) body))
                       (define (lambda-fixed-args f) (check-and-extract-form f (`(lambda (,args ... . ,_) ,_ ...) args) (`(lambda ,_ ,_ ...) null)))
                       (define (lambda-any-arg f) (check-and-extract-form f (`(lambda (,_ ... . ,arg) ,_ ...) arg) (`(lambda ,arg ,_ ...) arg)))

                       (define (begin? l) (tagged-with? 'begin l))
                       (define (begin-body f) (check-and-extract-form f `(begin ,body ...) body))

                       (define (quote? l) (tagged-with? 'quote l))
                       (define (quote-datum f) (check-and-extract-form f `(quote ,datum) datum))

                       (define (if? l) (tagged-with? 'if l))
                       (define (if-test f) (check-and-extract-form f `(if ,test ,_ ...) test))
                       (define (if-first-branch f) (check-and-extract-form f (`(if ,_ ,first ,_) first) (`(if ,_ ,first) first)))
                       (define (if-second-branch f) (check-and-extract-form f (`(if ,_ ,_ ,second) second) (`(if ,_ ,_) _void)))

                       (define (typical-amb? l) (tagged-with? 'amb l))
                       (define (ramb? l) (tagged-with? 'ramb l))
                       (define (amb? l) (or (ramb? l) (typical-amb? l)))
                       (define (amb-choices f) (check-and-extract-form f `(,_ ,choices ...) choices))

                       (define (catch? l) (tagged-with? 'catch l))
                       (define (catch-body f) (check-and-extract-form f `(catch ,body ,_) body))
                       (define (catch-else f) (check-and-extract-form f `(catch ,_ ,else) else))

                       (define (expression? _) #t) ;;A non-empty list can always be considered as an expression
                       (define (expression-operator l) (car l))
                       (define (expression-operands l) (cdr l)))))
  )

;;Selectors with result checking
(begin-encourage-inline
  (define (n:define-id f) (check-primitive-part 'identifier (define-id f) amb-variable?))
  (define (n:define-val f) (check-primitive-part 'value (define-val f) not-define?))
  (define (n:set!-id f) (check-primitive-part 'identifier (set!-id f) amb-variable?))
  (define (n:set!-val f) (check-primitive-part 'value (set!-val f) not-define?))
  (define (n:begin-body f) (check-primitive-part '|begin body| (begin-body f) non-empty-list?))
  (define (n:lambda-fixed-args f) (check-primitive-part '|fixed arguments| (lambda-fixed-args f) (listof amb-variable?)))
  (define (n:lambda-any-arg f) (check-primitive-part '|any arguments| (lambda-any-arg f) (or/c null amb-variable?)))
  (define (n:lambda-body f) (check-primitive-part '|lambda body| (lambda-body f) non-empty-list?))
  (define (n:if-test f) (check-primitive-part 'test (if-test f) not-define?))
  (define (n:if-first-branch f) (check-primitive-part 'then (if-first-branch f) not-define?))
  (define (n:if-second-branch f) (check-primitive-part 'else (if-second-branch f) not-define?))
  (define (n:quote-datum f) (quote-datum f))
  (define (n:amb-choices f) (check-primitive-part '|amb choices| (amb-choices f) (listof not-define?)))
  (define (n:catch-body f) (check-primitive-part '|catch body| (catch-body f) not-define?))
  (define (n:catch-else f) (check-primitive-part '|catch else| (catch-else f) not-define?))
  (define (n:expression-operator f) (check-primitive-part 'operator (expression-operator f) not-define?))
  (define (n:expression-operands f) (check-primitive-part 'operands (expression-operands f) (listof not-define?)))
  )
;;--------------------------

;;Arity handling
(begin-encourage-inline
  ;;Arguments
  (define (arguments? v) (list? v))
  (define (get-arguments-num o) (length o))
  (define (get-arguments-list o) o)
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
  (define (make-closure env fixed any body)
    (__closure env (if any (- -1 (length fixed)) (arithmetic-shift 1 (length fixed))) fixed any body))
  (define (get-procedure-arity-mask p)
    (cond ((procedure? p) (procedure-arity-mask p))
          (else (__closure-mask p))))
  (define (any-number-of-arguments? mask)
    (= mask -1))
  (define (arity-include? mask n)
    (bitwise-bit-set? mask n))
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
                (cond ((let ((expanded (environment-expand f e)))
                         (if (__expander_box? expanded)
                             expanded
                             #f))
                       =>
                       ;;You have to handle identifiers yourself
                       (lambda (b) (plain-expand (__expander_box-expression b) e)))
                      ((or (amb-variable? f) (amb-self-evaluating? f)) f)
                      ((if? f) (make-if (plain-expand (n:if-test f) e)
                                        (plain-expand (n:if-first-branch f) e)
                                        (plain-expand (n:if-second-branch f) e)))
                      ((define? f) (make-define (n:define-id f)
                                                (plain-expand (n:define-val f) e)))
                      ((set!? f) (make-set! #:permanent? (permanent-set!? f) (n:set!-id f) (plain-expand (n:set!-val f) e)))
                      ((begin? f) (make-begin (append-primitive-sequence-body (map (lambda (f) (plain-expand f e)) (n:begin-body f)))))
                      ((lambda? f)
                       (define fixed (n:lambda-fixed-args f))
                       (define any (n:lambda-any-arg f))
                       (cond ((check-duplicates (cons any fixed) eq?) => (lambda (name) (raise (exn:fail:amb:syntax:primitive (format "Duplicate argument name: ~a" name) (current-continuation-marks))))))
                       (make-lambda (make-lambda-args fixed any)
                                    (expand-primitive-internal-sequence (map (lambda (f) (plain-expand f e)) (n:lambda-body f)))))
                      ((quote? f) f)
                      ((amb? f) (make-amb #:random? (ramb? f) (map (lambda (c) (plain-expand c e)) (n:amb-choices f))))
                      ((catch? f) (make-catch (plain-expand (n:catch-body f) e) (plain-expand (n:catch-else f) e)))
                      ((expression? f) (make-expression (plain-expand (n:expression-operator f) e)
                                                        (map (lambda (f) (plain-expand f e)) (n:expression-operands f))))
                      (else (raise (exn:fail:amb:syntax (format "Malformed form: ~s" f) (current-continuation-marks)))))))
             (expand-amb
              (lambda (f e)
                ;;Checking
                (cond ((not (__environment? e)) (raise (exn:fail:amb:contract (format "~s is not an environment value" e) (current-continuation-marks)))))
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
                (cond ((amb-self-evaluating? exp) (lambda (_ succeed fail) (succeed exp fail)))
                      ((amb-variable? exp) (lambda (env succeed fail) (succeed (environment-lookup-variable env exp) fail)))

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
                       (define fixed (lambda-fixed-args exp))
                       (define any (lambda-any-arg exp))
                       (define body-proc (analyze-sequence (lambda-body exp)))
                       (lambda (env succeed fail)
                         (succeed (make-closure env fixed any body-proc) fail)))
                      ((set!? exp)
                       (define id (set!-id exp))
                       (define val-proc (analyze-primitive-form (set!-val exp)))
                       (define typical? (typical-set!? exp))
                       (lambda (env succeed fail)
                         (val-proc
                          env
                          (lambda (v fail1)
                            (define old (environment-assign-variable! env id v))
                            (succeed _void (lambda () (cond (typical? (environment-assign-variable! env id old))) (fail1))))
                          fail)))
                      ((define? exp)
                       (define id (define-id exp))
                       (define val-proc (analyze-primitive-form (define-val exp)))
                       (lambda (env succeed fail)
                         (val-proc
                          env
                          (lambda (v fail1)
                            (succeed (environment-define-variable! env id v) fail1))
                          fail)))
                      ((amb? exp)
                       (define choice-procs (map analyze-primitive-form (amb-choices exp)))
                       (define resolved-choice-procs (if (ramb? exp) (shuffle choice-procs) choice-procs))
                       (lambda (env succeed fail)
                         (define (try-next choices)
                           (if (null? choices)
                               (fail)
                               ((car choices) env succeed (lambda () (try-next (cdr choices))))))
                         (try-next resolved-choice-procs)))
                      ((catch? exp)
                       (define body-proc (analyze-primitive-form (catch-body exp)))
                       (define else-proc (analyze-primitive-form (catch-else exp)))
                       (lambda (env succeed fail)
                         (body-proc env (lambda (val fail1) (succeed val fail1)) (lambda () (else-proc env succeed fail)))))

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

                      (else (raise (exn:fail:amb:syntax (format "Malformed form: ~s" exp)) (current-continuation-marks))))))

             (eval-primitive-form (lambda (exp env succeed fail) ((analyze-primitive-form exp) env succeed fail)))
             (plain-eval (lambda (exp env succeed fail) (eval-primitive-form (expand-amb exp env) env succeed fail)))

             (plain-apply
              (lambda (operator operands succeed fail)
                ;;Checking
                (cond ((not (arguments? operands))
                       (raise (exn:fail:amb:contract (format "~s cannot be supplied as by-position arguments" operands) (current-continuation-marks))))
                      ((not (amb-procedure? operator))
                       (raise (exn:fail:amb:contract:applicable (format "~s is not an applicable object" operator) (current-continuation-marks))))
                      ((let ((mask (get-procedure-arity-mask operator))) (not (or (any-number-of-arguments? mask) #;"Avoid unneccessary checking" (arity-include? mask (get-arguments-num operands)))))
                       (raise-arity operator (get-procedure-arity-mask operator) (get-arguments-num operands))))
                ;;Application
                (define arguments-list (get-arguments-list operands))
                (cond ((procedure? operator)
                       (succeed (apply operator arguments-list) fail))
                      (else
                       (define-values (fixed-binding-list rest)
                         (for/fold ((r null) (v arguments-list))
                                   ((n (in-list (__closure-fixed operator))))
                           (values (cons (cons n (car v)) r) (cdr v))))
                       (define any-name (__closure-any operator))
                       (define binding-list (cond ((amb-variable? any-name) (cons (cons any-name rest) fixed-binding-list))
                                                  (else fixed-binding-list)))
                       (define env (environment-add-frame (__closure-env operator) binding-list))
                       ((__closure-body operator) env succeed fail)))))

             ;;Default success and failure handlers
             (default-succeed (lambda (v _) v))
             (default-fail (lambda () (raise (exn:fail:amb:ambiguous "There are no more choices" (current-continuation-marks)))))

             ;;Exported environment constructors
             (fixed-bindings
              (list (cons 'expand expand-amb)))
             (make-optimal-base-environment
              (lambda ((assoc null) #:succeed (succeed default-succeed) #:fail (fail default-fail) #:expander (expander (lambda _ #f)))
                (define new
                  (make-environment
                   #:expander expander
                   (append
                    (list (cons 'apply (lambda (exp env) (plain-apply exp env succeed fail)))
                          (cons 'eval (lambda (exp env) (plain-eval exp env succeed fail)))
                          (cons 'the-global-environment (lambda () new))
                          (cons 'make-base-environment (lambda () (make-example-base-environment #:fail fail #:succeed succeed))))
                    fixed-bindings
                    assoc)))
                new))
             (more-fixed-bindings
              (list (cons '+ +)
                    (cons '- -)
                    (cons '* *)
                    (cons '/ /)
                    (cons 'add1 add1)
                    (cons 'sub1 sub1)
                    (cons 'abs abs)
                    (cons 'number? number?)
                    (cons 'real? real?)
                    (cons 'rational? rational?)
                    (cons 'integer? integer?)
                    (cons '< <)
                    (cons '> >)
                    (cons '= =)
                    (cons '<= <=)
                    (cons '>= >=)
                    (cons 'eq? eq?)
                    (cons 'car car)
                    (cons 'cdr cdr)
                    (cons 'cons cons)
                    (cons 'list list)
                    (cons 'null null)
                    (cons 'null? null?)
                    (cons 'list? list?)
                    (cons 'bytes? bytes?)
                    (cons 'list->bytes list->bytes)
                    (cons 'bytes->list bytes->list)
                    (cons 'bytes=? bytes=?)
                    (cons 'bytes>? bytes>?)
                    (cons 'bytes<? bytes<?)
                    (cons 'bytes-ref bytes-ref)
                    (cons 'not not)
                    ;;Renamed
                    (cons 'primitive? amb-primitive?)
                    (cons 'procedure? amb-procedure?)
                    (cons 'self-evaluating? amb-self-evaluating?)
                    (cons 'void __void)
                    (cons 'void? __void?)
                    ))
             (example-expander ;;Works only when the default representation is used
              (lambda (exp c)
                (define (make-let assoc body)
                  (cons 'let (cons assoc body)))
                (define (make-delay e)
                  (cons 'delay e))
                (match exp
                  (`(let ((,id ,expr) ...) ,body ...)
                   (c (make-expression (make-lambda id body) expr)))
                  (`(let* (,assoc ...) ,body ...)
                   (c (car (foldl (lambda (a b) (list (make-let (list a) b))) body (reverse assoc)))))
                  (`(letrec ((,id ,expr) ...) ,body ...)
                   (c (make-let null (cons (make-begin (map (lambda (i e) (make-define i e)) id expr)) body))))
                  (`(define (,name . ,args) ,body ...)
                   (c (make-define name (make-lambda args body))))
                  (`(cond (,test ,body ...) ... (else ,else-body ...))
                   (c (foldl (lambda (t b e) (make-if t (make-begin b) e))
                             (make-begin else-body)
                             (reverse test)
                             (reverse body))))
                  (`(cond (,test ,body ...) ...)
                   (c (foldl (lambda (t b e) (make-if t (make-begin b) e))
                             _void
                             (reverse test)
                             (reverse body))))
                  (`(delay ,e ...)
                   (c
                    (make-let (list (list 'run? #f) (list 'result #f) (list 'thunk (make-lambda null e)))
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
                  (`(cons-stream ,a ,d)
                   (c (make-let (list (list 'immed a) (list 'promise (make-delay (list d)))) (list (make-lambda '(proc) (list (make-expression 'proc (list 'immed 'promise))))))))
                  (`(and ,branches ...)
                   (c (foldl (lambda (b t) (make-let (list (list 'test b)) (list (make-if 'test t 'test))))
                             'test
                             (reverse branches))))
                  (`(or ,branches)
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
                    (define map (let ((cons cons) (foldl foldl) (null null) (reverse reverse)) (lambda (proc l) (reverse (foldl (lambda (e i) (cons (proc e) i)) null l)))))
                    (define member (let ((car car) (cdr cdr) (null? null?)) (lambda (val items cpr) (cond ((null? items) #f) ((cpr (car items) val) items) (else (member val (cdr items) cpr))))))
                    (define filter (let ((cons cons) (null null) (foldl foldl) (reverse reverse)) (lambda (pred ls) (reverse (foldl (lambda (v s) (if (pred v) (cons v s) s)) null ls)))))
                    (define append (let ((foldl foldl) (cons cons) (reverse reverse)) (lambda (l1 l2) (foldl cons l2 (reverse l1)))))
                    (define append* (let ((foldl foldl) (append append) (null null)) (lambda (ll) (foldl append null (reverse ll)))))
                    (define cartesian-product
                      (let ((append* append*) (map map) (cons cons) (apply apply) (car car) (cdr cdr) (null? null?))
                        (lambda ll
                          (if (null? ll)
                              '(())
                              (append* (map (lambda (v) (map (lambda (r) (cons v r)) (apply cartesian-product (cdr ll)))) (car ll)))))))

                    (define (force promise) (promise))

                    (define stream-car (let ((scar (lambda (a d) a))) (lambda (s) (s scar))))
                    (define stream-cdr (let* ((force force) (scdr (lambda (a d) (force d)))) (lambda (s) (s scdr))))
                    (define stream-empty? null?)
                    (define empty-stream null)
                    (define stream-map
                      (let ((ormap ormap)
                            (stream-empty? stream-empty?)
                            (empty-stream empty-stream)
                            (apply apply)
                            (map map)
                            (stream-car stream-car)
                            (stream-cdr stream-cdr)
                            (cons cons))
                        (lambda (proc . sl) (if (ormap stream-empty? sl) empty-stream (cons-stream (apply proc (map stream-car sl)) (apply stream-map (cons proc (map stream-cdr sl))))))))
                    (define stream-ref
                      (let ((= =) (stream-car stream-car) (stream-cdr stream-cdr) (sub1 sub1))
                        (lambda (s n)
                          (if (= n 0)
                              (stream-car s)
                              (stream-ref (stream-cdr s) (sub1 n))))))
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
  (check-true (amb-self-evaluating? 1.2))
  (check-true (amb-procedure? +))
  (check-true (expression? (default:make-expression '+ '(2 2))))
  ;;Exceptions
  (check-not-exn (lambda () (expand-amb (list (list 1)) (make-optimal-base-environment))))
  (check-exn exn:fail:amb:syntax:primitive? (lambda () (checked:set!-id (default:make-set! '(+ 1 2) 3))))
  (check-exn exn:fail:amb:syntax:primitive? (lambda () (checked:begin-body (default:make-begin null))))
  (check-exn exn:fail:amb:syntax:primitive? (lambda () (checked:lambda-fixed-args (default:make-lambda '(+ 1) '((+ 1 2))))))
  (check-exn exn:fail:amb:syntax:primitive? (lambda () (checked:define-val (default:make-define 'a (default:make-define 'b 1)))))
  (check-exn exn:fail:amb:syntax:unbound? (lambda () (eval-amb '(+) (make-optimal-base-environment))))
  (check-exn exn:fail:amb:contract:applicable? (lambda () (eval-amb '(+) (make-optimal-base-environment (list (cons '+ 0))))))
  (check-exn exn:fail:amb:contract:arity? (lambda () (eval-amb '((lambda (n) (+ n 1))) (make-optimal-base-environment (list (cons '+ +))))))
  (check-exn exn:fail:amb:contract? (lambda () (eval-amb '(+ "") (make-optimal-base-environment (list (cons '+ +))))))
  (check-exn exn:fail:amb:contract? (lambda () (eval-amb '(+ 1 2) null)))
  (check-exn exn:fail:amb:contract? (lambda () (expand-amb '(+ 1 2) null)))
  (check-exn exn:fail:amb:contract? (lambda () (apply-amb (eval-amb '(lambda () 1) (make-example-base-environment)) (vector))))
  ;;Selectors
  (check-eq? (checked:define-id (default:make-define 'a 1)) 'a)
  (check-equal? (checked:if-test (default:make-if '(+ 1 2) 1 2)) '(+ 1 2))
  (check-equal? (checked:quote-datum (default:make-quote '(1 . 2))) '(1 . 2))
  ;;Expansion, evaluation and application
  (define env (make-example-base-environment))
  (check-true (= (eval-amb '((lambda (n) (cond ((>= n 0) n) (else (- n)))) -1) env) 1))
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
  (check-true (let ((result (eval-amb
                             '(let ((caught #t))
                                (catch (let ((a (ramb 1 2 3)))
                                         (require (integer? (/ a 2)))
                                         (permanent-set! caught #f)
                                         (cons caught a))
                                  (cons caught 4)))
                             env)))
                (or (and (car result) (= (cdr result) 4))
                    (and (not (car result)) (= (cdr result) 2)))))
  ;;Benchmark
  (define-runtime-module-path-index namespace-module '(submod ".." namespace))
  (define-namespace-anchor anchor)
  (define ns (module->namespace namespace-module (namespace-anchor->empty-namespace anchor)))
  (define benchmark1
    '(begin
       (define amb-traverse
         (time
          (eval-amb
           '(lambda (l) (reverse (map add1 l)))
           (make-example-base-environment))))
       (define racket-traverse
         (time (eval '(lambda (l) (reverse (map add1 l))))))
       (let ((lst (range 0 200000)))
         (check-equal? (time (apply-amb amb-traverse (list lst)))
                       (time (apply racket-traverse (list lst)))))))
  (pretty-write benchmark1)
  (eval benchmark1 ns)
  (define benchmark2
    '(begin
       (define amb-pi-stream-10000th
         (time
          (eval-amb
           '(begin
              (define odds/+- (cons-stream 1 (stream-map (lambda (n) (if (< n 0) (- 2 n) (- (+ n 2)))) odds/+-)))
              (define pi-stream
                (cons-stream (stream-car odds/+-) (stream-map (lambda (o p) (+ (/ 1 o) p)) (stream-cdr odds/+-) pi-stream)))
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
       (check-true (= racket-pi-stream-10000th amb-pi-stream-10000th))))
  (pretty-write benchmark2)
  (eval benchmark2 ns)
  (define benchmark3
    '(begin
       (define optimal-multiple-dwelling
         (time
          (let ((all (box null)))
            (eval-amb
             '(let ((baker (amb 1 2 3 4 5)))
                (require (not (= baker 5)))
                (let ((fletcher (amb 1 2 3 4 5)))
                  (require (and (not (= fletcher baker)) (not (= fletcher 1)) (not (= fletcher 5))))
                  (let ((smith (amb 1 2 3 4 5)))
                    ;;Exercise 4.38
                    (require (and (not (= smith baker)) (not (= smith fletcher)) #;(not (= (abs (- smith fletcher)) 1))))
                    (let ((cooper (amb 1 2 3 4 5)))
                      (require (and (not (= cooper baker)) (not (= cooper fletcher)) (not (= cooper smith)) (not (= (abs (- fletcher cooper)) 1)) (not (= cooper 1))))
                      (let ((miller (amb 1 2 3 4 5)))
                        (require (and (not (= miller baker)) (not (= miller fletcher)) (not (= miller smith)) #;(not (= miller cooper)) (> miller cooper)))
                        (list baker fletcher smith cooper miller))))))
             (make-example-base-environment)
             (lambda (v f) (cons v (f)))
             (lambda () null)))))
       (define typical-multiple-dwelling
         (time
          (eval-amb
           '(let ((baker '(1 2 3 4 5))
                  (fletcher '(1 2 3 4 5))
                  (smith '(1 2 3 4 5))
                  (cooper '(1 2 3 4 5))
                  (miller '(1 2 3 4 5)))
              (define (distinct? items)
                (cond ((null? items) #t)
                      ((null? (cdr items)) #t)
                      ((member (car items) (cdr items) =) #f)
                      (else (distinct? (cdr items)))))
              (filter (lambda (p)
                        (let ((baker (car p))
                              (fletcher (car (cdr p)))
                              (smith (car (cdr (cdr p))))
                              (cooper (car (cdr (cdr (cdr p)))))
                              (miller (car (cdr (cdr (cdr (cdr p)))))))
                          (and (distinct? p)
                               (not (= baker 5))
                               (not (= cooper 1))
                               (not (= fletcher 1))
                               (not (= fletcher 5))
                               (> miller cooper)
                               ;;Exercise 4.38
                               #;(not (= 1 (abs (- smith fletcher))))
                               (not (= 1 (abs (- fletcher cooper)))))))
                      (cartesian-product baker fletcher smith cooper miller)))
           (make-example-base-environment))))
       (check-equal? optimal-multiple-dwelling typical-multiple-dwelling)))
  (pretty-write benchmark3)
  (eval benchmark3 ns))
