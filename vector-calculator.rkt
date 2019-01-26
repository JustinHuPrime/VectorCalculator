#lang racket

;; SIMD Calculator

;; expression = vector
;;            | number
;;            | identifier
;;            | '{' '+' expression { expression } '}'
;;            | '{' '-' expression { expression } '}'
;;            | '{' '*' expression { expression } '}'
;;            | '{' '/' expression expression { expression } '}'
;;            | '{' 'let' identifier expression '}'
;;            | '{' 'begin' expression { expression } '}'

;; vector = '{' { number } '}'
;; identifier = ? racket symbol ?
;; number = ? racket number ?

(struct expression ())
(struct vector expression (values))
(struct num expression (value))
(struct id expression (name))
(struct add expression (expressions))
(struct sub expression (from bys))
(struct mult expression (expressions))
(struct div expression (numerator denominators))
(struct def expression (id expression))
(struct beg expression (expressions))

(define (reserved-id? symbol)
  (ormap (curry eqv? symbol) '(+ - * / let begin)))

(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(? symbol?) (if (reserved-id? sexp)
                     (error (format "Use of reserved id ~s" (symbol->string sexp)))
                     (id sexp))]
    [(and (? list?) (? (curry andmap number?))) (vector sexp)]
    [(cons '+ exprs) (add (map parse exprs))]
    [(cons '- (cons from bys)) (sub (parse from) (map parse bys))]
    [(cons '* exprs) (mult (map parse exprs))]
    [(cons '/ (cons num denoms)) (div (parse num) (map parse denoms))]
    [(list 'let (? symbol? id) expr) (def id (parse expr))]
    [(cons 'begin (cons expr exprs)) (beg (map parse (cons expr exprs)))]
    [else (error (format "Could not parse \"~s\"" sexp))]))

(struct value ())
(struct vector-val value (values))
(struct number-val value (value))

(struct eval-error (msg curr-env))

(define (eval expr env)
  (cond [(vector? expr) (values (vector-val (vector-values expr)) env)]
        [(num? expr) (values (number-val (num-value expr)) env)]
        [(id? expr) (if (dict-has-key? env (id-name expr))
                        (values (dict-ref env (id-name expr)) env)
                        (raise (eval-error (format "No such id ~s" (symbol->string (id-name expr))) env)))]
        [(add? expr)
         (let* ([values+renv (foldl (λ (expr v+e)
                                      (let*-values ([(out-value out-env) (eval expr (cdr v+e))])
                                        (cons (append (car v+e) (list out-value)) out-env)))
                                    (let-values ([(fval fenv) (eval (first (add-expressions expr)) env)])
                                      (cons (list fval) fenv))
                                    (rest (add-expressions expr)))]
                [vals (car values+renv)]
                [renv (cdr values+renv)])
           (cond [(andmap vector-val? vals) (if (andmap (compose (curry =
                                                                        (length (vector-val-values (first vals))))
                                                                 length
                                                                 vector-val-values)
                                                        (rest vals))
                                                (values (vector-val (foldl (λ (vector-v rsf)
                                                                             (map + (vector-val-values vector-v) rsf))
                                                                           (vector-val-values (first vals))
                                                                           (rest vals)))
                                                        renv)
                                                (raise (eval-error "Attempted to add vectors of non-uniform length." renv)))]
                 [(andmap number-val? vals) (values (number-val (foldl (λ (num-v rsf)
                                                                         (+ (number-val-value num-v) rsf))
                                                                       0
                                                                       vals))
                                                    renv)]
                 [else (raise (eval-error "Attempted to mix scalar and vector addition." renv))]))]
        [(sub? expr)
         (if (empty? (sub-bys expr))
             (let-values ([(result renv) (eval (sub-from expr) env)])
               (if (number-val? result)
                   (values (number-val (- (number-val-value result))) renv)
                   (values (vector-val (map - (vector-val-values result))) renv)))
             (let*-values ([(from-val fenv) (eval (sub-from expr) env)]
                           [(by-vals+renv) (foldl (λ (expr v+e)
                                                    (let-values ([(out-value out-env) (eval expr (cdr v+e))])
                                                      (cons (append (car v+e) (list out-value)) out-env)))
                                                  (let-values ([(fval fenv) (eval (first (sub-bys expr)) env)])
                                                    (cons (list fval) fenv))
                                                  (rest (sub-bys expr)))]
                           [(by-vals) (car by-vals+renv)]
                           [(renv) (cdr by-vals+renv)])
               (cond [(and (number-val? from-val) (andmap number-val? by-vals))
                      (values (number-val (apply - (map number-val-value (cons from-val by-vals)))) renv)]
                     [(and (vector-val? from-val) (andmap vector-val? by-vals))
                      (if (andmap (compose (curry = (length (vector-val-values from-val)))
                                           length
                                           vector-val-values)
                                  by-vals)
                          (values (vector-val (foldl (λ (vector-v rsf)
                                                       (map - rsf (vector-val-values vector-v)))
                                                     (vector-val-values from-val)
                                                     by-vals))
                                  renv)
                          (raise (eval-error "Attempted to subtract vectors of non-uniform length." renv)))]
                     [else (raise (eval-error "Attempted to mix scalar and vector subtraction." renv))])))]
        [(mult? expr)
         (let* ([factors+renv (foldl (λ (expr v+e)
                                       (let-values ([(out-value out-env) (eval expr (cdr v+e))])
                                         (cons (append (car v+e) (list out-value)) out-env)))
                                     (let-values ([(fval fenv) (eval (first (mult-expressions expr)) env)])
                                       (cons (list fval) fenv))
                                     (rest (mult-expressions expr)))]
                [factors (car factors+renv)]
                [renv (cdr factors+renv)])
           (cond [(andmap number-val? factors)
                  (values (number-val (foldl (λ (num-v rsf)
                                               (* (number-val-value num-v) rsf))
                                             1
                                             factors))
                          renv)]
                 [(= 1 (count vector-val? factors))
                  (let ([vector (findf vector-val? factors)]
                        [numbers (remf vector-val? factors)])
                    (values (vector-val (foldl (λ (n rsf)
                                                 (map (curry * (number-val-value n)) rsf))
                                               (vector-val-values vector)
                                               numbers))
                            renv))]
                 [else (raise (eval-error "Attempted to multiply vectors." renv))]))]
        [(div? expr)
         (let*-values ([(num-val fenv) (eval (div-numerator expr) env)]
                       [(denom-vals+renv) (foldl (λ (expr v+e)
                                                   (let-values ([(out-value out-env) (eval expr (cdr v+e))])
                                                     (values (append (car v+e) (list out-value)) out-env)))
                                                 (let-values ([(fval fenv) (eval (first (div-denominators expr)) env)])
                                                   (cons (list fval) fenv))
                                                 (rest (div-denominators expr)))]
                       [(denom-vals) (car denom-vals+renv)]
                       [(renv) (cdr denom-vals+renv)])
           (if (andmap number-val? denom-vals)
               (if (number-val? num-val)
                   (values (number-val (apply / (map number-val-value (cons num-val denom-vals))))
                           renv)
                   (values (vector-val (foldl (λ (n rsf)
                                                (map (curryr / (number-val-value n)) rsf))
                                              (vector-val-values num-val)
                                              denom-vals))
                           renv))
               (raise (eval-error "Attempted to divide by a vector." renv))))]
        [(def? expr)
         (let-values ([(val renv) (eval (def-expression expr) env)])
           (values val (dict-set renv (def-id expr) val)))]
        [(beg? expr)
         (let ([val+renv (foldl (λ (expr v+e)
                                  (let-values ([(nval nenv) (eval expr (cdr v+e))])
                                    (cons nval nenv)))
                                (let-values ([(fval fenv) (eval (first (beg-expressions expr)) env)])
                                  (cons (list fval) fenv))
                                (rest (beg-expressions expr)))])
           (values (car val+renv) (cdr val+renv)))]))


(define (repl)
  (let loop ([env empty])
    (display "> ")
    (let ([line (read-line)])
      (if (eof-object? line)
	  (void)
	  (with-handlers ([eval-error? (compose loop eval-error-curr-env)])
	    (let*-values ([(lexed-line) (with-handlers ([exn:fail? (λ (e)
								      (displayln (format "Could not parse '~a'." line) (current-error-port))
								      (raise (eval-error "retry" env)))])
						       (read (open-input-string line)))]
			  [(parsed-line) (with-handlers ([exn:fail? (λ (e)
								       (displayln (exn-message e) (current-error-port))
								       (raise (eval-error "retry" env)))])
							(parse lexed-line))]
			  [(result new-env) (with-handlers ([eval-error? (λ (e)
									    (displayln (eval-error-msg e) (current-error-port))
									    (raise e))])
							   (eval parsed-line env))])
	      (if (vector-val? result)
		  (displayln (vector-val-values result))
		  (displayln (number-val-value result)))
	      (loop new-env)))))))

(command-line #:args () (repl))
