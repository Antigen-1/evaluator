#lang racket/base

(module+ test
  (require rackunit))

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

(require racket/generic racket/match (for-syntax racket/base))

;;Exceptions
(struct exn:fail:scheme exn:fail ())
(struct exn:fail:scheme:syntax exn:fail:scheme ())

;;Macros
(define-syntax (check-and-extract-form stx)
  (syntax-case stx ()
    ((_ val pattern id)
     #'(match val
         (pattern id)
         (_ (raise (exn:fail:scheme:syntax (format "Malformed scheme form: ~s" val) (current-continuation-marks))))))
    ((_ val pattern id pred)
     #'(match val
         (pattern #:when (pred id) id)
         (_ (raise (exn:fail:scheme:syntax (format "Malformed scheme form: ~s" val) (current-continuation-marks))))))))

;;Utilities
(define (not-define? f) (not (define? f)))
(define (last-expr? lst)
  ;;Ensure that the last form is not a define form
  (match lst
    ((list _ ... last) #:when (not-define? last) #t)
    (_ #f)))
(define (non-empty-list? l) (and (list? l) (not (null? l))))
(define (primitive? f) (or (exact-integer? f) (boolean? f) (symbol? f) (null? f) (string? f)))
(define (simple-representation? f)
  (or (primitive? f) (and (pair? f) (simple-representation? (car f)) (simple-representation? (cdr f)))))

;;Special forms
;;Only syntax are checked here
(define forms '(define set! lambda begin quote if))
(define-generics define-form
  (define? define-form)
  (define-id define-form)
  (define-val define-form)
  #:defaults ((simple-representation?
               (define (define? l) (and (non-empty-list? l) (eq? 'define (car l))))
               (define (define-id f) (check-and-extract-form f (list 'define id _) id symbol?))
               (define (define-val f) (check-and-extract-form f (list 'define _ val) val not-define?)))))
(define-generics set!-form
  (set!? set!-form)
  (set!-id set!-form)
  (set!-val set!-form)
  #:defaults ((simple-representation?
               (define (set!? l) (and (non-empty-list? l) (eq? 'set! (car l))))
               (define (set!-id f) (check-and-extract-form f (list 'set! id _) id symbol?))
               (define (set!-val f) (check-and-extract-form f (list 'define _ val) val not-define?)))))
(define-generics lambda-form
  (lambda? lambda-form)
  (lambda-args lambda-form)
  (lambda-body lambda-form)
  #:defaults ((simple-representation?
               (define (lambda? l) (and (non-empty-list? l) (eq? 'lambda (car l))))
               (define (lambda-args f) (check-and-extract-form f (list 'lambda (list args ...) _ ...) args (lambda (l) (andmap symbol? l))))
               (define (lambda-body f) (check-and-extract-form f (list 'lambda (list _ ...) body ...) body last-expr?)))))
(define-generics begin-form
  (begin? begin-form)
  (begin-body begin-form)
  #:defaults ((simple-representation?
               (define (begin? l) (and (non-empty-list? l) (eq? 'begin (car l))))
               (define (begin-body f) (check-and-extract-form f (list 'begin body ...) body last-expr?)))))
(define-generics quote-form
  (quote? quote-form)
  (quote-datum quote-form)
  #:defaults ((simple-representation?
               (define (quote? l) (and (non-empty-list? l) (eq? 'quote (car l))))
               (define (quote-datum f) (check-and-extract-form f (list 'quote datum) datum)))))
(define-generics if-form
  (if? if-form)
  (if-test if-form)
  (if-first-branch if-form)
  (if-second-branch if-form)
  #:defaults ((simple-representation?
               (define (if? l) (and (non-empty-list? l) (eq? 'if (car l))))
               (define (if-test f) (check-and-extract-form f (list 'if test first second) test not-define?))
               (define (if-first-branch f) (check-and-extract-form f (list 'if test first second) first not-define?))
               (define (if-second-branch f) (check-and-extract-form f (list 'if test first second) second not-define?)))))

;;Application
(define-generics s-exp
  (expression? s-exp)
  (expression-operator s-exp)
  (expression-operand s-exp)
  #:defaults ((simple-representation?
               (define (expression? l) (or (primitive? l) (and (non-empty-list? l) (not (ormap (lambda (h) (eq? h (car l))) forms)))))
               (define (expression-operator l) (car l))
               (define (expression-operand l) (cdr l)))))

(module+ test
  ;; Any code in this `test` submodule runs when this file is run using DrRacket
  ;; or with `raco test`. The code here does not run when this file is
  ;; required by another module.

  ;;Predicates
  (check-true (simple-representation? '(+ 1 2)))
  (check-false (simple-representation? 1.2))
  (check-true (primitive? "a"))
  (check-false (primitive? #"a"))
  (check-true (expression? '(+ 2 2)))
  ;;Exceptions
  (check-exn exn:fail:scheme:syntax? (lambda () (set!-id '(set! (+ 1 2) 3))))
  (check-exn exn:fail:scheme:syntax? (lambda () (begin-body '(begin (+ 1 2) (define a 1)))))
  (check-exn exn:fail:scheme:syntax? (lambda () (lambda-args '(lambda (+ 1) (+ 1 2)))))
  ;;Selectors
  (check-equal? (if-test '(if (+ 1 2) 1 2)) '(+ 1 2))
  (check-equal? (quote-datum ''(1 . 2)) '(1 . 2)))
