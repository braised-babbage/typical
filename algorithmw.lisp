;;; Hindley-Milner style type inference.
;;;
;;; At a high level, the problem we want to solve is something like
;;; this: given a term in the untyped lambda calculus, can we recover
;;; the "most general" type (aka 'principal type scheme') for the
;;; term? The code below implements the famous 'Algorithm W', which
;;; solves this problem in the slightly more general case allowing for
;;; let-polymorphism. It is based on a Scala implementation
;;; presented by Odersky in Chapter 16 of Scala by Example. For more
;;; information, see the bibliography at the end.

(declaim (optimize (debug 3)))

;;; Types


;;; A type is one of the following:
;;;    - a type variable (a non-null symbol)
;;;    - an arrow (-> t1 t2) where t1,t2 are types
;;;    - a type constructor (foo t1 ...)


(defun free-variables (type)
  "Return a list of free variables in the given type."
  (if (symbolp type)
      (list type)
      ;; either -> or a type constructor
      (remove-duplicates (mappend #'free-variables (rest type)))))

;;; A substitution is an alist mapping type variables to types.

(defun substitute-types (subst type)
  "Replace type variables with their values in the given type."
  (if (symbolp type)			; type variable
      (let ((val (lookup subst type)))
	   (if val
	       (substitute-types subst val)
	       type))
      ;; either -> or a type constructor
      (cons (first type)	       
	    (mapcar #'(lambda (type) (substitute-types subst type))
		    (rest type)))))

;;; The type inference algorithm requires that we be able to unify types.

(defun unify (u v &optional (subst nil))
  "Compute a substitution making two types equal, if possible."
  (let ((su (substitute-types subst u))
	(sv (substitute-types subst v)))
    (cond ((or (null su) (null sv))
	   (error "cannot unify ~a and ~a" u v))
	  ((and (symbolp su) (symbolp sv) (eq su sv))
	   subst)
	  ((and (symbolp su) (not (member su (free-variables sv))))
	   (extend subst su sv))
	  ((symbolp sv)
	   (unify v u subst))
	  ((eq (first su) (first sv))
	   (unify-all (rest su) (rest sv) subst))
	  (t  (error "cannot unify ~a and ~a" u v)))))

(defun unify-all (ts us subst)
  "Unify two lists of types, successively extending an initial
substitution."
  (cond ((and (null ts) (null us))
	 subst)
	((or (null ts) (null us))
	 (error "cannot unify sequences of mismatched length"))
	(t (let ((subst2 (unify (first ts) (first us) subst)))
	     (unify-all (rest ts) (rest us) subst2)))))



;;; Type Schemes are basically types with some quantified type variables.
;;; For example, \forall a (-> a a).

(defstruct type-scheme
  "A type scheme consists of a type and some universally quantified type variables."
  vars type)

(defun new-instance (scheme)
  "Replace the bound variables of a type scheme with a fresh set."
  (let* ((vars (type-scheme-vars scheme))
	 (fresh (mapcar #'make-type-variable vars))
	 (subst (extend nil vars fresh)))
    (substitute-types subst (type-scheme-type scheme))))

(defvar *variable-count* 0)

(defun make-type-variable (&optional (prefix 't))
  "Make a fresh type variable with the given prefix."
  (intern (format nil "~a~d" prefix (incf *variable-count*))))


;;; Helper functions, used for managing
;;;   - substitutions (mapping type variables to types)
;;;   - type contexts (mapping variables to type schemes)

(defun lookup (env var)
  (let ((binding (assoc var env)))
    (when binding
      (cdr binding))))

(defun extend (env vars vals)
  (if (listp vars)
      (pairlis vars vals env)
      (acons vars vals env)))


(defun mappend (fn list)
  "Append the results of calling fn on each element of list.
  Like mapcon, but uses append instead of nconc."
  (apply #'append (mapcar fn list)))



;;; Terms
;;; A term in our language is one of the following:
;;;   - variable (a non-null symbol)

;;;   - lambda term (lambda (x) body)
;;;     where x is a variable and body is a term
(defun lambda-var (expr)
  (first (second expr)))
(defun lambda-body (expr)
  (third expr))

;;;   - let term (let ((x e)) body)
;;;      where x is a variable, e is a term, and body is a term
(defun let-binding (expr)
  (first (second expr)))
(defun let-body (expr)
  (third expr))
(defun let-var (expr)
  (first (let-binding expr)))
(defun let-val (expr)
  (second (let-binding expr)))

;;;   - an application (e f)
;;;     where e,f are terms
(defun application-op (expr)
  (first expr))
(defun application-arg (expr)
  (second expr))


;;; A type context is a mapping from variable terms to type schemes,
;;; represented as an alist. The following lifts the substitution
;;; operation to contexts.

(defun substitute-all (subst context)
  "Return a new type context, with the given substitution applied
pointwise to all of the type schemes."
  (mapcar #'(lambda (binding)
	      (let* ((var (car binding))
		     (scm (cdr binding))
		     (bound (type-scheme-vars scm))
		     (new-type (substitute-types subst (type-scheme-type scm))))
		; assumes bound variables don't appear in subst
		(cons var (make-type-scheme :vars bound :type new-type))))
	  context))

;;; There are two natural ways to get a type scheme from a type.
;;; The simplest is to consider the type scheme with no quantified variables.
;;; For the inference algorithm, we also need the following:

(defun gen-scheme (type &optional (context nil))
  "Given a type and a type context, construct type scheme which quantifies
any free variables of the type which are not free in the context."
  (let ((env-free (loop for (var . scheme) in context
		     appending (free-variables (type-scheme-type scheme)))))
    (make-type-scheme :vars (set-difference (free-variables type) env-free)
		      :type type)))


;;; Algorithm W


(defun principal-substitution (context term type &optional (subst nil))
  "Given a type context, a term, and a type, constructs a substitution 
   under which the type is a 'principal type scheme' for the term with respect
   to the type context."
  (if (symbolp term)
      (principal-substitution-variable context term type subst)
      (case (first term)
	(LAMBDA (principal-substitution-lambda context (lambda-var term) (lambda-body term) type subst))
	(LET    (principal-substitution-let context (let-var term) (let-val term) (let-body term) type subst))
	(otherwise (principal-substitution-application context (application-op term) (application-arg term) type subst)))))

(defun principal-substitution-variable (context var type subst)
  (let ((scheme (lookup context var)))
    (if scheme
	(unify (new-instance scheme) type subst)
	(error "undefined: ~a" var))))

(defun principal-substitution-application (context op arg type subst)
  (let* ((a (make-type-variable))
	 (subst2 (principal-substitution context op (list '-> a type) subst)))
    (principal-substitution context arg a subst2)))

(defun principal-substitution-lambda (context var body type subst)
  (let* ((a (make-type-variable))
	 (b (make-type-variable))
	 (subst2 (unify type (list '-> a b) subst))
	 (context2 (extend context var (make-type-scheme :type a))))
    (principal-substitution context2 body b subst2)))

(defun principal-substitution-let (context var val body type subst)
  (let* ((a (make-type-variable))
	 (subst2 (principal-substitution context val a subst))
	 (context2 (extend context
			   var
			   (gen-scheme (substitute-types subst2 type)
				       (substitute-all subst2 context)))))
    (principal-substitution context2 body type subst2)))


;;; Here are some defaults to play around with.

(defparameter *default-type-context* nil)

(defun define-type (term type)
  (push (cons term (gen-scheme type)) *default-type-context*))

(setq *default-type-context* nil)
(define-type 'true '(boolean))
(define-type 'false '(boolean))
(define-type 'if    '(-> (boolean) (-> a (-> a a))))  ; Everything is curried!
(define-type 'zero  '(integer))
(define-type 'succ  '(-> (integer) (integer)))
(define-type 'empty '(list a))
(define-type 'cons  '(-> a (-> (list a) (list a))))
(define-type 'isEmpty '(-> (list a) (boolean)))
(define-type 'head  '(-> (list a) a))
(define-type 'tail '(-> (list a) (list a)))
(define-type 'fix '(-> a (-> a a)))


;;; The front-end.

(defun infer-type (term &optional (context *default-type-context*))
  (let* ((a (make-type-variable))
	 (subst (principal-substitution context term a)))
    (substitute-types subst a)))


;;; Bibliography
;;;

;;; Clément, D., Despeyroux, T., Kahn, G., & Despeyroux, J. (1986, August). A simple applicative language: Mini-ML.
;;;      In Proceedings of the 1986 ACM conference on LISP and functional programming (pp. 13-27). ACM

;;; Damas, L., & Milner, R. (1982, January). Principal type-schemes for functional programs.
;;;      In Proceedings of the 9th ACM SIGPLAN-SIGACT symposium on Principles of programming languages (pp. 207-212). ACM

;;; Garnock-Jones, T. (2012). Type Inference for ML.
;;;      http://www.ccs.neu.edu/home/amal/course/7480-s12/inference-notes.pdf

;;; Odersky, M. (2011). Scala by example.
;;;      http://www.scala-lang.org/docu/files/ScalaByExample.pdf

;;; Pottier, F., & Rémy, D. (2005). The essence of ML type inference.
;;;      http://gallium.inria.fr/~fpottier/publis/emlti-final.pdf

;;; Wand, M. (1987). A simple algorithm and proof for type inference.
;;;      Fundamenta Informaticae, 10(2), 115-121.

