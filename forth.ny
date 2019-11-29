;;;;;;;;; Forth a la Let over Lambda ;;;;;;;;

(defvar forth-registers
  '(pstack rstack pc dict compiling dtable))

(defun sym (&rest strs)
  (intern (string-upcase (apply #'strcat (mapcar #'string strs)))))

(defmacro defstruct (name &rest slots)
  (let ((n -1))
    `(progn
       ,@(mapcar (lambda (slot)
		   (incf n)
		   `(defmacro ,(sym name "-" slot)
			(struct)
		      (list 'aref struct ,n)))
		 slots)
       (defun ,(sym "make-" name)
	   (&key ,@slots)
	 (vector ,@slots)))))

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
(setq forth-prim-forms nil)

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

(def-forth-prim dup nil
  (push (car pstack) pstack))

(def-forth-prim swap nil
  (let ((s0 (pop pstack))
	(s1 (pop pstack)))
    (push s0 pstack)
    (push s1 pstack)))

(def-forth-prim print nil
  (print (pop pstack)))

(def-forth-prim to-r nil
  (push (pop pstack) rstack))

(def-forth-prim from-r nil
  (push (pop rstack) pstack))

(defmacro go-forth (forth &rest words)
  `(dolist (w ',words)
     (funcall ,forth w)))

(defun go-forth-q (forth &rest words)
  (dolist (w words)
    (funcall forth w)))

(setq forth-stdlib nil)

(defmacro forth-stdlib-add (&rest all)
  `(setf forth-stdlib
	 (nconc forth-stdlib
		',all)))

(defun butlast (xs)
  (let (ys)
    (dotimes (n (1- (length xs)))
      (push (nth n xs) ys))
    (reverse ys)))

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
     (t (error "Unknown pandric get " sym))))

(defun pandriclet-set (letargs)
  `(case sym
     ,@(mapcar #'(lambda (x)
		   `(,(car x) (setq ,(car x) val)))
	       letargs)
     (t (error "Unknown pandric get " sym))))

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

(defmacro forth-handle-not-found ()
  `(cond
     ((and (consp v) (eq (car v) 'quote))
      (if compiling
	  (forth-compile-in (cadr v))
	  (push (cadr v) pstack)))
     ((and (consp v) (eq (car v) 'postpone))
      (let ((word (forth-lookup (cadr v) dict)))
	(when (not word)
	  (error "Postpone failed " (cadr v)))
	(forth-compile-in (forth-word-thread word))))
     ((symbolp v)
      (error "Word not found " v))
     (t
      (if compiling
	  (forth-compile-in v)
	  (push v pstack)))))
