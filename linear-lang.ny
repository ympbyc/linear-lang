;nyquist plug-in
;version 4
;type analyze
;categories "http://lv2plug.in/ns/lv2core#AnalyserPlugin"
;name "Linear a linear programming language"
;action "Running Linear"
;info "by Minori Yamashita ympbyc@gmail.com.\nReleased under GPL v2.\n"

;; linear-lang.ny by Minori Yamashita 2019
;;
;; For information about writing and modifying Nyquist plug-ins:
;; http://wiki.audacityteam.org/wiki/Nyquist_Plug-ins_Reference

;control noise-gate "noise-gate" float "" 0.2 0.0 1.0
;control mode "mode" choice "[dev]preprocess, [dev]frequency graph, [dev]reconstruct, recognition, save words" 0
;control avg "average" int "" 100 1 1000
;control words "words" string "" ""

;;ref:http://audacity.238276.n2.nabble.com/Processing-individual-samples-td238764.html

(load "forth.ny")

(setq *project-srate* 16000)

;; define a dsp class
;;
(setf sq-class (send class :new '(copy-of-sound osc noise-gate)))

;; initial function of dsp class
;;
(send sq-class :answer :isnew '(sound noise)
      '((setf copy-of-sound (snd-copy sound))
	(setf noise-gate noise)
	(setf osc (osc-pulse 1 0))))

;; method to be executed with every call to dsp-class
;;
(send sq-class :answer :next '()
      '((let ((current-sample (snd-fetch copy-of-sound)))
	  (when current-sample
	    (if (< current-sample noise-gate)
		(progn (snd-fetch osc) 0.0)
		(abs (snd-fetch osc)))))))

(describe 'frequency-stream "sound * int * float -> vector")
(defun frequency-stream (sound srate duration)
  (let ((delayed-arr    (make-array (round (* srate duration))))
	(last-sample    0)
	(current-sample 0)
	(n              0)
	(m              0)
	(n*             0))
    (while (setq current-sample (snd-fetch sound))
      (when (and (<= last-sample 0.5) (> current-sample 0.5)) ;;rising edge?
	(while (and (>= m 0) (null (aref delayed-arr m)))
	  (setf (aref delayed-arr m) (/ srate (- n n*)))
	  (setq m (1- m)))
	(setq n* n))
      (setf (aref delayed-arr n) nil)
      (setq n (1+ n))
      (setq m n))
    delayed-arr))


;; define a dsp class
;;
(setf freq-class (send class :new '(copy-of-sound srate arr count)))

;; initial function of dsp class
;;
(send freq-class :answer :isnew '(sound rate dura)
      '((setf copy-of-sound (snd-copy sound))
	(setf srate rate)
	(setf count -1)
	(setf arr (frequency-stream sound rate dura))))

;; method to be executed with every call to dsp-class
;;
(send freq-class :answer :next '()
      '((let ((current-sample (snd-fetch copy-of-sound)))
	  (when current-sample
	    (setf count (1+ count))
	    (/ (min 4000 (or (aref arr count) 0)) 4000)))))

(setf recon-class (send class :new '(copy-of-sound srate osc last-hz phase)))

(send recon-class :answer :isnew '(sound rate)
      '((setf copy-of-sound (snd-copy sound))
	(setf srate rate)
	(setf osc (osc-pulse 0 0))
	(setf last-hz 0)
	(setf phase 0)))

(send recon-class :answer :next '()
      '((let* ((current-sample (snd-fetch copy-of-sound))
	       (hz (* (or current-sample 0) 4000)))
	  (when current-sample
	    (when (> (abs (- hz last-hz)) 5)
	      (setf osc (osc-pulse hz 0))
	      (setf last-hz hz))
	    (snd-fetch osc)))))

(describe 'sq "sound -> sound")
(defun sq (sound)
  (let* ((srate (snd-srate sound))
	 (obj   (send sq-class :new sound noise-gate))
	 (snd   (snd-fromobject (snd-t0 sound) srate obj)))
    snd))

(describe 'freq "sound -> sound")
(defun freq (sound)
  (let* ((srate (snd-srate sound))
	 (snd   (lp (sq sound) 2000))
	 (obj   (send freq-class :new snd srate (get-duration 1))))
    (snd-avg (snd-fromobject (snd-t0 snd) srate obj)
	     avg 1 OP-AVERAGE)))

(describe 'reconstruct "sound -> sound")
(defun reconstruct (sound)
  (let* ((srate (snd-srate sound))
	 (snd   (freq sound))
	 (obj   (send recon-class :new snd srate)))
    (snd-fromobject (snd-t0 snd) srate obj)))

(describe 'find-stops "sound -> ((int . int))")
(defun find-stops (sound)
  (let ((sound (snd-copy sound))
	(srate (snd-srate sound))
	smpl
	(silence 0)
	(cnt 0)
	(audible-start 0)
	audible
	ranges)
    (while (setq smpl (snd-fetch sound))
      (setq cnt (1+ cnt))
      (if (< smpl 0.1)
	  (setq silence (1+ silence))
	  (progn
	    (setq silence 0)
	    (unless audible
	      (setq audible-start cnt)
	      (setq audible t))))
      (when (and audible  (> silence (/ srate 3)))
	(push (cons (/ audible-start srate)
		    (/ (- cnt silence) srate))
	      ranges)
	(setq silence 0)
	(setq audible nil)))
    (reverse ranges)))


(describe 'split-words "sound -> (sound)")
(defun split-words (sound)
  (let ((stops (find-stops sound))
	(t0    (snd-t0 sound))
	(srate (snd-srate sound)))
    (mapcar (lambda (tn)
	      (extract-abs (- (car tn) t0)
			   (- (cdr tn) t0)
			   (cue sound)))
	    stops)))

(describe '*words* "((symbol . sound))")
(setq *words* ())

(defun word-name (pair) (car pair))
(defun word-snd (pair) (cdr pair))

(describe 'sl "sound -> float")
(defun sl (sound) (float (snd-length sound ny:all)))

(describe 'match "sound * sound -> float")
(defun match (w word)
  (let* ((distance 0)
	 w1 w2
	 (sr1 (snd-srate w))
	 (sr2 (snd-srate word))
	 l)
    (if (not (= sr1 sr2)) (error "sample rate mismatch" (list sr1 sr2)))
    (if (< (sl w) (sl word))
	(progn (setq w1 (snd-copy w)) (setq w2 (snd-copy word)))
	(progn (setq w1 (snd-copy word)) (setq w2 (snd-copy w))))
    (setq w2 (force-srate (round (* sr1 (/ (sl w1) (sl w2)))) w2))
    (setq l (sl w1))
    (if (not (= (sl w1) (sl w2))) (error "shrinking error" (sl w1) (sl w2)))
    (while (setq smpl (snd-fetch w1))
      (setq distance (+ distance
			(abs (- smpl (snd-fetch w2))))))
    (/ distance l)))


(describe 'reads "string -> (string)")
(defun reads (string)
  (let (str
	(strm (make-string-input-stream string))
	strs)
    (while (setq str (read strm))
      (push str strs))
    (reverse strs)))

(describe *word-names* "(string)")
(setq *word-names* ())


(describe 'save-words "((sound . symbol)) -> IO ()")
(defun save-words (words)
  (setq *words* (append *words* words))
  (format t "WORDS: ~A" *words*)
  (setq *workspace* nil)
  (add-to-workspace '*word-names*)
  (dolist (w words)
    (s-save (word-snd w) (* *project-srate* 5)
	    (format nil "~A.wav" (word-name w))
	    snd-head-Wave
	    nil nil nil t)
    (push (word-name w) *word-names*))
  (save-workspace))


(describr 'init-words "-> IO ()")
(defun init-words ()
  (load "workspace")
  (dolist (wn *word-names*)
    (push (cons wn
		(s-read (format nil "~A.wav" wn)))
	  *words*)))


(describe 'extract-and-save-words "sound * string -> IO sound")
(defun extract-words (sound word-names)
  (let* ((freq  (freq (sq sound)))
	 (ws    (split-words freq)))
    (save-words (mapcar #'cons
			(reads word-names) ws))
    freq))


(describe 'recognition "sound -> ((float . symbol))")
(defun recognition (word-sound)
  (sort
   (mapcar (lambda (w)
	     (cons (match w word-sound) (word-name w)))
	   *words*)
   (lambda (x y) (< (car x) (car y)))))


(setq linear-lang (new-forth))

(describe 'process "sound -> IO sound")
(defun process (sound)
  (init-words)
  (let ((sound (force-srate *project-srate* sound)))
    (cond ((= mode 0)
	   (sq sound))
	  ((= mode 1)
	   (freq (sq sound)))
	  ((= mode 2)
	   (reconstruct (freq (sq sound))))
	  ((= mode 3)
	   (let ((ws  (split-words (freq (sq sound))))
		 (rec (mapcar #'word-name (mapcar #'recognition xs))))
	     (go-forth-q linear-lang rec)
	     nil))
	  ((= mode 4)
	   (extract-and-save-words sound words)))))


(multichan-expand #'process *TRACK*)

