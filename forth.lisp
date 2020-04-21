(defpackage lol-forth
  (:use :cl))
(in-package :lol-forth)
;;;;;;;;; Forth a la Let over Lambda ;;;;;;;;

(defvar forth-registers
  '(pstack rstack pc dict compiling dtable))

(defun sym (&rest strs)
  (intern (string-upcase (apply #'concatenate 'string (mapcar #'string strs)))))

(defstruct forth-word
  name prev immediate thread)

(defun forth-lookup (w last)
  (when last
    (if (eql (forth-word-name last) w)
	last
      (forth-lookup
       w (forth-word-prev last)))))

(defmacro forth-inner-interpreter ()
  `(do ()
       ((and (null pc) (null rstack)))
       (cond ((functionp (car pc))
	      (funcall (car pc)))
	     ((consp (car pc))
	      (push (cdr pc) rstack)
	      (setf pc (car pc)))
	     ((null pc)
	      (setf pc (pop rstack)))
	     (t
	      (push (car pc) pstack)
	      (setf pc (cdr pc))))))

;; Prim-form: (name immediate . forms)
(defparameter forth-prim-forms nil)

(defmacro def-forth-naked-prim (&rest code)
  `(push ',code forth-prim-forms))

(defmacro def-forth-prim (&rest code)
  `(def-forth-naked-prim
     ,@code
     (setf pc (cdr pc))))

(defmacro def-forth-prim-binary (name op)
  `(def-forth-prim ,name nil
     (push (,op (pop pstack) (pop pstack))
	   pstack)))

(def-forth-prim nop nil)

(def-forth-prim-binary * *)
(def-forth-prim-binary + +)
(def-forth-prim-binary - -)
(def-forth-prim-binary / /)
(def-forth-prim-binary rem rem)
(def-forth-prim-binary < <)
(def-forth-prim-binary > >)
(def-forth-prim-binary <= <=)
(def-forth-prim-binary >= >=)
(def-forth-prim-binary mul *)
(def-forth-prim-binary add +)
(def-forth-prim-binary sub -)
(def-forth-prim-binary div /)
(def-forth-prim-binary mod rem)
(def-forth-prim-binary lessthan <)
(def-forth-prim-binary greaterthan >)
(def-forth-prim-binary lessthanequal <=)
(def-forth-prim-binary greaterthanequal >=)

(def-forth-prim drop nil
  (pop pstack))

(def-forth-prim dot nil
  (print (pop pstack)))

(def-forth-prim dup nil
  (push (car pstack) pstack))

(def-forth-prim swap nil
  (let ((s0 (pop pstack))
	(s1 (pop pstack)))
    (push s0 pstack)
    (push s1 pstack)))

(def-forth-prim rot nil
  (let ((s0 (pop pstack))
	(s1 (pop pstack))
	(s2 (pop pstack)))
    (push s0 pstack)
    (push s2 pstack)
    (push s1 pstack)))

(def-forth-prim print nil
  (print (car pstack)))

(def-forth-prim to-r nil
  (push (pop pstack) rstack))

(def-forth-prim from-r nil
  (push (pop rstack) pstack))

(defmacro go-forth (forth &rest words)
  `(go-forth-q ,forth '(,@words)))

(defmacro let1 (var val &body body)
  `(let ((,var ,val))
     ,@body))

(defun go-forth-q (forth words)
  (let1 result
	(dolist (w words)
	  (funcall forth w))
    (format t "~%PSTACK:    ~s~%RSTACK:    ~s~%PC:        ~s~%COMPILING: ~s"
	    (funcall forth :pandric-get 'pstack)
	    (funcall forth :pandric-get 'rstack)
	    (funcall forth :pandric-get 'pc)
	    (funcall forth :pandric-get 'compiling))
    result))

(defparameter forth-stdlib nil)

(defmacro forth-stdlib-add (&rest all)
  `(setf forth-stdlib
	 (nconc forth-stdlib
		',all)))

(defmacro alet (letargs &rest body)
  `(let (this
	 ,@letargs)
     (setq this ,@(last body))
     ,@(butlast body)
     (lambda (&rest params)
       (apply this params))))

(defmacro dlambda (&rest ds)
  (let ((gargs (gensym)))
    `(lambda (&rest ,gargs)
       (case (car ,gargs)
	 ,@ (mapcar
	     (lambda (d)
	       `(,(if (eq t (car d))
		      t
		      (list (car d)))
		  (apply (lambda ,@ (cdr d))
			 ,(if (eq t (car d))
			      gargs
			      `(cdr ,gargs)))))
	     ds)))))

(defun pandriclet-get (letargs)
  `(case sym
     ,@(mapcar #'(lambda (x) `(,(car x) ,(car x)))
	       letargs)
     (t (error "Unknown pandric get ~s" sym))))

(defun pandriclet-set (letargs)
  `(case sym
     ,@(mapcar #'(lambda (x)
		   `(,(car x) (setq ,(car x) val)))
	       letargs)
     (t (error "Unknown pandric get ~s" sym))))

(defmacro plambda (largs pargs &rest body)
  (let ((pargs (mapcar #'list pargs)))
    `(let (this self)
       (setq
	this (lambda ,largs ,@body)
	self (dlambda
	      (:pandric-get (sym)
			    ,(pandriclet-get pargs))
	      (:pandric-set (sym val)
			    ,(pandriclet-set pargs))
	      (t (&rest args)
		 (apply this args)))))))

(defmacro new-forth ()
  `(alet ,forth-registers
	 (setq dtable '())
	 (forth-install-prims)
	 (dolist (v forth-stdlib)
	   (funcall this v))
	 (plambda (v) ,forth-registers
		   (let ((word (forth-lookup v dict)))
		       (if word
			   (forth-handle-found)
			   (forth-handle-not-found))))))

(defmacro forth-install-prims ()
  `(progn
     ,@(mapcar
	(lambda (a1)
	  `(let ((thread (lambda () ,@ (cddr a1))))
	     (setf dict
		   (make-forth-word
		    :name ',(car a1)
		    :prev dict
		    :immediate ,(cadr a1)
		    :thread thread))
	     (setf dtable
		   (cons thread ',(cddr a1)))))
	forth-prim-forms)))

(def-forth-prim [ t  ; <- t means immediate
  (setf compiling nil))

(def-forth-prim ] nil ; <- not immediate
  (setf compiling t))

(defmacro forth-compile-in (v)
  `(setf (forth-word-thread dict)
	 (nconc (forth-word-thread dict)
		(list ,v))))

(defmacro forth-handle-found ()
  `(if (and compiling
	    (not (forth-word-immediate word)))
       (forth-compile-in (forth-word-thread word))
       (progn
	 (setf pc (list (forth-word-thread word)))
	 (forth-inner-interpreter))))

;;(sym/n 'map/2) => '(map 2)
(defun sym/arity (sym)
  (let1 xs
      (uiop:split-string (symbol-name sym)
			 :separator "/")
    (values (sym (car xs))
	    (if (cadr xs)
		(parse-integer (cadr xs))
		1))))

(defmacro handle-unknown-symbol ()
  `(multiple-value-bind (fname arity)
       (sym/arity v)
     (if (fboundp fname)
	 (let1 res
	     (apply
	      (symbol-function fname)
	      (loop for i from 1 to arity
		 collect (pop pstack)))
	   (push res pstack))
	 (error "Word not found ~s" v))))

(defmacro forth-handle-not-found ()
  `(cond
     ((and (consp v) (eq (car v) 'quote))
      (if compiling
	  (forth-compile-in (cadr v))
	  (push (cadr v) pstack)))
     ((and (consp v) (eq (car v) 'postpone))
      (let ((word (forth-lookup (cadr v) dict)))
	(when (not word)
	  (error "Postpone failed ~s" (cadr v)))
	(forth-compile-in (forth-word-thread word))))
     ((symbolp v)
      (handle-unknown-symbol))
     (t
      (if compiling
	  (forth-compile-in v)
	  (push v pstack)))))

(defun pstack (forth)
  (funcall forth :pandric-get 'pstack))

(print "lol-forth loaded.")

(defparameter lolf (new-forth))
(defmacro lolf (&rest words)
  `(go-forth lolf ,@words))
