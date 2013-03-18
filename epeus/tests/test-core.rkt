#lang racket

;;; Tests for the tiny-clos module.

(require "../core.rkt")
(require (submod "../core.rkt" test-exports))
(require rackunit)
(require rackunit/text-ui)

(provide epeus-core-suite)

(define-test-suite epeus-core-suite)
  
