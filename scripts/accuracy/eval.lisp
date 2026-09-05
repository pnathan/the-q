;;; eval.lisp -- independent oracle for the-q transcendentals, in exact rational
;;; arithmetic snapped to a 2^-160 grid.  Usage: sbcl --script eval.lisp dump.tsv

(defparameter *g* (expt 2 160))
(defun rnd (x) (/ (round (* x *g*)) *g*))

;;; --- reference functions ---------------------------------------------------

(defun exp-small (r)                    ; |r| <= 1/2
  (loop with term = 1 with sum = 1
        for k from 1 to 70
        do (setf term (rnd (/ (* term r) k))) (incf sum term)
        finally (return (rnd sum))))
(defparameter *e* (rnd (expt (exp-small 1/2) 2)))
(defun rexp (x)
  (let* ((n (round x)) (f (- x n)))
    (rnd (* (expt *e* n) (exp-small f)))))

(defun atanh-series (z)                 ; |z| <= 1/3
  (loop with p = z with sum = z
        for j from 1 to 80
        do (setf p (rnd (* p z z))) (incf sum (/ p (+ 1 (* 2 j))))
        finally (return (rnd sum))))
(defparameter *ln2* (rnd (* 2 (atanh-series 1/3))))
(defun rln (x)                          ; x > 0
  (let ((k 0))
    (loop while (>= x 2) do (setf x (/ x 2)) (incf k))
    (loop while (< x 1) do (setf x (* x 2)) (decf k))
    (rnd (+ (* k *ln2*) (* 2 (atanh-series (/ (- x 1) (+ x 1))))))))
(defparameter *ln10* (rln 10))

(defun rsqrt (x) (/ (isqrt (floor (* x *g* *g*))) *g*))
(defun icbrt (n)
  (if (< n 2) n
      (let ((r (ash 1 (ceiling (integer-length n) 3))))
        (loop (let ((s (floor (+ (* 2 r) (floor n (* r r))) 3)))
                (when (>= s r) (return r))
                (setf r s))))))
(defun rcbrt (x)
  (let ((m (/ (icbrt (floor (* (abs x) *g* *g* *g*))) *g*)))
    (if (< x 0) (- m) m)))

;; pi by Machin, exact series, then snapped at 2^-224 (headroom for n <= 2^20).
(defun atan-inv-exact (n terms)
  (loop with x = (/ 1 n) with p = x with sum = x
        for j from 1 to terms
        do (setf p (/ p (* n n)))
           (if (oddp j) (decf sum (/ p (+ 1 (* 2 j)))) (incf sum (/ p (+ 1 (* 2 j)))))
        finally (return sum)))
(defparameter *pi* (let ((g (expt 2 224)))
                     (/ (round (* g (- (* 16 (atan-inv-exact 5 80)) (* 4 (atan-inv-exact 239 40))))) g)))

(defun sin-series (r)
  (loop with p = r with sum = r
        for j from 1 to 45
        do (setf p (rnd (/ (* p r r -1) (* 2 j (+ 1 (* 2 j)))))) (incf sum p)
        finally (return (rnd sum))))
(defun cos-series (r)
  (loop with p = 1 with sum = 1
        for j from 1 to 45
        do (setf p (rnd (/ (* p r r -1) (* (- (* 2 j) 1) (* 2 j))))) (incf sum p)
        finally (return (rnd sum))))
(defun reduce-trig (x)                  ; -> (values r n)
  (let* ((n (round (/ x (/ *pi* 2)))) (r (rnd (- x (* n (/ *pi* 2))))))
    (values r (mod n 4))))
(defun rsin (x)
  (multiple-value-bind (r q) (reduce-trig x)
    (ecase q (0 (sin-series r)) (1 (cos-series r)) (2 (- (sin-series r))) (3 (- (cos-series r))))))
(defun rcos (x)
  (multiple-value-bind (r q) (reduce-trig x)
    (ecase q (0 (cos-series r)) (1 (- (sin-series r))) (2 (- (cos-series r))) (3 (sin-series r)))))
(defun rtan (x) (rnd (/ (rsin x) (rcos x))))

(defun atan-series (y)                  ; |y| <= 0.1
  (loop with p = y with sum = y
        for j from 1 to 45
        do (setf p (rnd (* p y y -1))) (incf sum (/ p (+ 1 (* 2 j))))
        finally (return (rnd sum))))
(defun ratan (x)
  (cond ((< x 0) (- (ratan (- x))))
        ((> x 1) (rnd (- (/ *pi* 2) (ratan (/ 1 x)))))
        (t (let ((y x))
             (dotimes (i 3) (setf y (rnd (/ y (+ 1 (rsqrt (+ 1 (* y y))))))))
             (rnd (* 8 (atan-series y)))))))
(defun rasin (x)
  (cond ((= x 1) (/ *pi* 2)) ((= x -1) (- (/ *pi* 2)))
        (t (ratan (/ x (rsqrt (- 1 (* x x))))))))
(defun racos (x) (rnd (- (/ *pi* 2) (rasin x))))
(defun ratan2 (y x)
  (cond ((> x 0) (ratan (/ y x)))
        ((< x 0) (if (>= y 0) (rnd (+ (ratan (/ y x)) *pi*)) (rnd (- (ratan (/ y x)) *pi*))))
        ((> y 0) (/ *pi* 2)) ((< y 0) (- (/ *pi* 2))) (t nil)))

(defun rsinh (x) (rnd (/ (- (rexp x) (rexp (- x))) 2)))
(defun rcosh (x) (rnd (/ (+ (rexp x) (rexp (- x))) 2)))
(defun rtanh (x) (rnd (/ (rsinh x) (rcosh x))))
(defun rexp2 (x) (let ((n (floor x))) (rnd (* (expt 2 n) (rexp (* (- x n) *ln2*))))))

(defun reference (name ins)
  (let ((x (first ins)) (y (second ins)))
    (cond
      ((string= name "pi") *pi*) ((string= name "half_pi") (/ *pi* 2))
      ((string= name "e") *e*) ((string= name "ln2") *ln2*)
      ((string= name "exp") (rexp x))
      ((string= name "ln") (and (> x 0) (rln x)))
      ((string= name "sqrt") (and (>= x 0) (rsqrt x)))
      ((string= name "cbrt") (rcbrt x))
      ((string= name "sin") (rsin x)) ((string= name "cos") (rcos x)) ((string= name "tan") (rtan x))
      ((string= name "atan") (ratan x))
      ((string= name "asin") (and (<= (abs x) 1) (rasin x)))
      ((string= name "acos") (and (<= (abs x) 1) (racos x)))
      ((string= name "atan2") (ratan2 x y))
      ((string= name "sinh") (rsinh x)) ((string= name "cosh") (rcosh x)) ((string= name "tanh") (rtanh x))
      ((string= name "exp2") (rexp2 x))
      ((string= name "log2") (and (> x 0) (rnd (/ (rln x) *ln2*))))
      ((string= name "log10") (and (> x 0) (rnd (/ (rln x) *ln10*))))
      ((string= name "pow_i32") (expt x y))
      ((string= name "powf") (and (> x 0) (rexp (* y (rln x)))))
      ((string= name "hypot") (rsqrt (+ (* x x) (* y y))))
      (t nil))))

;;; --- parsing ---------------------------------------------------------------

(defun split (s ch)
  (loop with start = 0 for pos = (position ch s :start start)
        collect (subseq s start pos) while pos do (setf start (1+ pos))))
(defun parse-frac (s) (let ((*read-eval* nil)) (values (read-from-string s))))
(defun parse-decimal (s)                ; "3.14159e-7" -> exact rational
  (let* ((epos (position-if (lambda (c) (member c '(#\e #\E))) s))
         (mant (subseq s 0 epos))
         (ex (if epos (parse-integer s :start (1+ epos)) 0))
         (neg (char= (char mant 0) #\-))
         (mant (string-left-trim "+-" mant))
         (dot (position #\. mant))
         (digits (remove #\. mant))
         (scale (if dot (- (length mant) dot 1) 0))
         (v (* (parse-integer digits) (expt 10 (- ex scale)))))
    (if neg (- v) v)))

(defun lg (v)
  (if (zerop v) "exact"
      (let* ((k (- (integer-length (numerator v)) (integer-length (denominator v))))
             (m (/ v (expt 2 k))))
        (format nil "2^~,3f" (+ k (log (coerce m 'double-float) 2d0))))))

;;; --- main ------------------------------------------------------------------

(defun main (path)
  (let ((pyref (make-hash-table :test 'equal))
        (worst-rel (make-hash-table :test 'equal))
        (worst-abs (make-hash-table :test 'equal))
        (oracle-gap (make-hash-table :test 'equal)))
    (with-open-file (in (concatenate (quote string) path ".pyref"))
      (loop for line = (read-line in nil) while line
            do (destructuring-bind (name inp ref) (split line #\Tab)
                 (setf (gethash (cons name inp) pyref) (parse-decimal ref)))))
    (flet ((bump (tbl key v inp) (when (> v (car (gethash key tbl '(0 . nil))))
                                   (setf (gethash key tbl) (cons v inp)))))
      (with-open-file (in path)
        (loop for line = (read-line in nil) while line
              do (destructuring-bind (name inp out) (split line #\Tab)
                   (when (and (find #\/ out) (not (search "special:" name)))
                     (let* ((ins (mapcar #'parse-frac (split inp #\,)))
                            (ref (reference name ins)))
                       (when ref
                         (let* ((got (parse-frac out))
                                (err (abs (- got ref)))
                                (rel (if (zerop ref) err (/ err (abs ref))))
                                (aerr (/ err (max 1 (abs ref))))
                                (py (gethash (cons name inp) pyref)))
                           (bump worst-rel name rel inp)
                           (bump worst-abs name aerr inp)
                           (when (member name '("sin" "cos" "tan") :test #'string=)
                             (let* ((ax (abs (first ins)))
                                    (key (format nil "~a ~a" name
                                                 (cond ((<= ax 1) "|x|<=1") ((<= ax 8) "|x|<=8")
                                                       ((<= ax 1024) "|x|<=2^10") (t "|x|<=2^20")))))
                               (bump worst-rel key rel inp) (bump worst-abs key aerr inp)))
                           (when py
                             (bump oracle-gap name
                                   (if (zerop ref) (abs (- py ref)) (/ (abs (- py ref)) (abs ref))) inp)))))))))
      (format t "~&~10a ~14a  ~24a ~22a  ~a~%" "function" "worst REL err" "at input" "worst err/max(1,|y|)" "at input")
      (let ((names (sort (loop for k being the hash-keys of worst-rel collect k) #'string<)))
        (dolist (n names)
          (let ((r (gethash n worst-rel)) (a (gethash n worst-abs)))
            (format t "~10a ~14a  ~24a ~22a  ~a~%" n (lg (car r)) (cdr r) (lg (car a)) (cdr a)))))
      (format t "~%Lisp-vs-mpmath oracle disagreement (worst relative, per function):~%")
      (let ((names (sort (loop for k being the hash-keys of oracle-gap collect k) #'string<)))
        (dolist (n names)
          (let ((g (gethash n oracle-gap)))
            (format t "  ~10a ~12a  at ~a~%" n (lg (car g)) (cdr g))))))))

(main (second sb-ext:*posix-argv*))
