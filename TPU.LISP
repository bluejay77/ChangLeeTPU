;;; -*- Mode: Common-LISP -*-
;;;
;;; Theorem Prover with Unit Binary Resolution
;;;
;;; From the Chang-Lee textbook Symbolic Logic and Mechanical Theorem
;;; Proving
;;;
;;; Chin-Liang Chang and Richard Char-Tung Lee:
;;; Symbolic Logic and Mechanical Theorem Proving
;;; Academic Press 1973, 0-12-170350-9
;;;
;;; Antti J Ylikoski 2015-11-20
;;;
;;; Corrected an error in the textbook program listing
;;; Have they actually run the code?
;;; AJY 2015-11-21
;;;
;;; This is the program from pp. 292--297 of the book, converted to the
;;; modern Common LISP
;;;
;;; And, examples 1--2 from pp. 298--300
;;;
;;;



(defun add1 (n) (+ n 1))
(defun sub1 (n) (- n 1))

(defvar *xlist* '(X1 X2 X3 X4 X5 X6 X7))

(defvar *ylist* '(Y1 Y2 Y3 Y4 Y5 Y6 Y7))

(defvar *zlist* '(ZZ1 ZZ2 ZZ3 ZZ4 ZZ5 ZZ6 ZZ7))

(defun rename (c xy)
  (declare (special *zlist*))
  (prog (var z)
     (setf z *zlist*)
     (setf var (cadr c))
     B1
     (cond ((null var) (go B2)))
     (setf c (subst (car z) (car var) c))
     (setf z (cdr z))
     (setf var (cdr var))
     (go B1)
     B2
     (setf z xy)
     (setf var (cadr c))
     B3
     (cond ((null var) (return c)))
     (setf c (subst (car z) (car var) c))
     (setf z (cdr z))
     (setf var (cdr var))
     (go B3)))


(defun inside (a e)
  (cond ((atom e) (equal a e))
    ((inside a (car e)) t)
    (t (inside a (cdr e)))))


(defun disagree (e1 e2)
  (cond ((null e1) nil)
	((or (atom e1) (atom e2))
	 (cond ((equal e1 e2) nil)
	       (t (list e1 e2))))
	((equal (car e1) (car e2))
	 (disagree (cdr e1) (cdr e2)))
	((or (atom (car e1)) (atom (car e2)))
	 (list (car e1) (car e2)))
	(t (disagree (car e1) (car e2)))))


	
(defun unification (e1 e2)
  (declare (special *xlist* *ylist*))
  (prog (d u d1 d2)
     (cond ((not (equal (length e1) (length e2)))
	    (return (quote no))))
     B1
     (setf d (disagree e1 e2))
     (cond ((null d) (return (reverse u))))
     (setf d1 (car d))
     (setf d2 (cadr d))
     (cond ((or (member d1 *xlist*) (member d1 *ylist*)) (go B3)))
     (cond ((or (member d2 *xlist*) (member d2 *ylist*)) (go B4)))
     B2
     (return (quote no))
     B3
     (cond ((inside d1 d2) (go B2)))
     (setf u (cons d u))
     (setf e1 (subst d2 d1 e1))
     (setf e2 (subst d2 d1 e2))
     (go B1)
     B4
     (cond ((inside d2 d1) (go B2)))
     (setf u (cons (reverse d) u))
     (setf e1 (subst d1 d2 e1))
     (setf e2 (subst d1 d2 e2))
     (go B1)))


(defun deletev (x y var)
  (prog (var1 tx tx1 x1)
     (setf x (append x y))
     B1
     (cond ((null var) (return x)))
     (setf var1 (car var))
     (setf tx x)
     (setf x1 nil)
     B2
     (cond ((null tx) (go B4)))
     (setf tx1 (car tx))
     (cond ((eq tx1 var1) (go B3)))
     (setf x1 (cons tx1 x1))
     (setf tx (cdr tx))
     (go B2)
     B3
     (setf x (append x1 (cdr tx)))
     B4
     (setf var (cdr var))
     (go B1)))


(defun uresolve (c1 c2 N)
  (declare (special *xlist* *ylist*))
  (prog (l1 l2 vc1 vc2 x y sign unif r res var v1 v2 h hist tc2)
     (setf c1 (rename c1 *xlist*))
     (setf c2 (rename c2 *ylist*))
     (setf l1 (car c1))
     (setf l2 (car c2))
     (setf vc1 (cadr c1))
     (setf vc2 (cadr c2))
     (setf c2 (caddr c2))
     (setf x (car (caddr c1)))
     (setf sign -1)
     (cond ((equal (car x) (quote not)) (go B7)))
     (setf sign 1)
     B1
     (cond ((null c2) (return (list (reverse res) (reverse hist) n))))
     (setf y (car c2))
     (cond ((equal (car y) (quote not)) (go B2)))
     (go B6)
     B2
     (setf unif (unification x (cdr y)))
     B3
     (cond ((equal unif (quote no)) (go B6)))
     (setf r (append (reverse tc2) (cdr c2)))
     (cond ((null r) (return (list (quote contradiction) l1 l2))))
     (setf var nil)
     B4
     (cond ((null unif) (go B5)))
     (setf v1 (caar unif))
     (setf v2 (cadar unif))
     (setf var (cons v1 var))
     (setf r (subst v2 v1 r))
     (setf unif (cdr unif))
     (go B4)
     B5
     (setf n (add1 n))
     (setf h (list n l1 l2 (add1 (length tc2))))
     (setf r (list n (deletev vc1 vc2 var) r))
     (setf res (cons r res))
     (setf hist (cons h hist))
     B6
     (setf tc2 (cons y tc2))
     (setf c2 (cdr c2))
     (cond ((equal sign 1) (go B1)))
     B7
     (cond ((null c2) (return (list (reverse res) (reverse hist) n))))
     (setf y (car c2))
     (cond ((equal (car y) (quote not)) (go B6)))
     (setf unif (unification (cdr x) y))
     (go B3)))


(defun gunit (s1 s2 w c n)
  (prog (l s3 ss3 w1 v u res hist m x)
     (cond ((null w) (return (list res hist n))))
     (setf l (length (caddr c)))
     (setf s3 (list (list 10000 c)))
     (setf ss3 s3)
     B1
     (cond ((null w) (go B7)))
     (setf w1 (car w))
     B2
     (cond ((null ss3) (go B4)))
     (setf v (car ss3))
     (cond ((> (car w1) (car v)) (go B3)))
     (setf u (uresolve w1 (cadr v) n))
     (cond ((null (car u)) (go B3)))
     (setf res (append res (car u)))
     (setf hist (append hist (cadr u)))
     (setf n (caddr u))
     B3
     (setf ss3 (cdr ss3))
     (go B2)
     B4
     (cond ((equal (sub1 l) 1) (go B6)))
     (setf m (car w1))
     B5
     (cond ((null res) (go B6)))
     (setf x (cons (list m (car res)) x))
     (setf res (cdr res))
     (go B5)
     B6
     (setf w (cdr w))
     (setf ss3 s3)
     (go B1)
     B7
     (setf l (sub1 l))
     (cond ((equal l 1) (return (list res hist n))))
     (setf s3 x)
     (setf ss3 s3)
     (setf x nil)
     (setf w (append s1 s2))
     (go B1)))


(defun pnsort (res)
  (prog (c pos neg)
   B1
   (cond ((null res) (return (list (reverse pos) (reverse neg)))))
   (setf c (caar (cddar res)))
   (cond ((equal (car c) (quote not)) (go B3)))
   (setf pos (cons (car res) pos))
   B2
   (setf res (cdr res))
   (go B1)
   B3
   (setf neg (cons (car res) neg))
   (go B2)))


(defun fdepth (c)
  (prog (n u)
     (setf c (car (caddr c)))
     (cond ((equal (car c) (quote not)) (go B1)))
     (setf c (cdr c))
     (go B2)
     B1
     (setf c (cddr c))
     B2
     (setf n 0)
     B3
     (cond ((null c) (go B5)))
     (cond ((atom (car c)) (go B4)))
     (setf u (append (cdar c) u))
     B4
     (setf c (cdr c))
     (go B3)
     B5
     (cond ((null u) (return n)))
     (setf n (add1 n))
     (setf c u)
     (setf u nil)
     (go B3)))


(defun ftest (res n4)
  (prog (c u)
     B1
     (cond ((null res) (return (reverse u))))
     (setf c (car res))
     (cond ((> (fdepth c) N4) (go B2)))
     (setf u (cons c u))
     B2
     (setf res (cdr res))
     (go B1)))



(defun subsume (c1 c2)
  (declare (special *xlist*)
	   (special *ylist*)
	   (special *zlist*))
  (prog (z var u)
     (setf c1 (rename c1 *xlist*))
     (setf c1 (car (caddr c1)))
     (setf z *zlist*)
     (setf var (cadr c2))
     (setf c2 (car (caddr c2)))
     B1
     (cond ((null var) (go B2)))
     (setf c2 (subst (car z) (car var) c2))
     (setf var (cdr var))
     (setf z (cdr z)) ; Here, corrected an error
     (go B1)
     B2
     (setf u (unification c1 c2))
     (cond ((equal u (quote no)) (return nil)))
     (return t)))


(defun stest (u res)
  (prog (r v w x1 y z)
   B1
   (cond ((null res) (go B5)))
   (setf r (car res))
   (setf z (append u v))
   B2
   (cond ((null z) (go B3)))
   (cond ((subsume (car z) r) (go B4)))
   (setf z (cdr z))
   (go B2)
   B3
   (setf v (cons r v))
   B4
   (setf res (cdr res))
   (go B1)
   B5
   (cond ((null v) (return w)))
   (setf x1 (car v))
   (setf z (cdr v))
   B6
   (cond ((null z) (go B8)))
   (cond ((subsume x1 (car z)) (go B7)))
   (setf y (cons (car z) y))
   B7
   (setf z (cdr z))
   (go B6)
   B8
   (setf w (cons x1 w))
   (setf v (reverse y))
   (setf y nil)
   (go B5)))


(defun contradict (u v)
  (prog (x1 y res)
     B1
     (cond ((or (null u) (null v)) (return nil)))
     (setf x1 (car u))
     (setf y v)
     B2
     (cond ((null y) (go B3)))
     (setq res (uresolve x1 (car y) -1))
     (cond ((equal (car res) (quote contradiction)) (return res)))
     (setf y (cdr y))
     (go B2)
     B3
     (setf u (cdr u))
     (go B1)))



(defun dtree (z hist n1)
  (prog (x tx x1 h m1 m2 m n)
     (setf hist (reverse hist))
     (setf x (cdr z))
     (setf z (list z))
     (cond ((> (car x) (cadr x)) (go B0)))
     (setf x (reverse x))
     B0
     (cond ((> (cadr x) N1) (go B1)))
     (setf x (list (car x)))
     B1
     (cond ((null x) (return z)))
     (setf x1 (car x))
     B2
     (cond ((equal x1 (caar hist)) (go B3)))
     (setf hist (cdr hist))
     (go B2)
     B3
     (setf x (cdr x))
     (setf h (car hist))
     (setf z (cons h z))
     (setf hist (cdr hist))
     (setf m1 (cadr h))
     (setf m2 (caddr h))
     (cond ((> m1 n1) (go B5)))
     B4
     (cond ((> m2 n1) (go B6)))
     (go B1)
     B5
     (setf n 1)
     (setf m m1)
     (go B7)
     B6
     (setf n 2)
     (setf m m2)
     B7
     (cond ((null x) (go B8)))
     (setf x1 (car x))
     (cond ((equal x1 m) (go B10)))
     (cond ((> x1 M) (go B9)))
     B8
     (setf x (append (reverse tx) (cons m x)))
     (go B11)
     B9
     (setf tx (cons x1 tx))
     (setf x (cdr x))
     (go B7)
     B10
     (setf x (append (reverse tx) z))
     B11
     (setf tx nil)
     (cond ((equal n 2) (go B1)))
     (go B4)))


;;; ------------------------------------------------------------

(defun tpu (s1 s2 s3 w n1 n2 n3 n4)
  (prog (s w1 ts u1 u n k ck wck v pos neg hist y x1 x)
     (setf s (append s1 s2))
     (setf s (reverse s))
     B1
     (cond ((null w) (go B6)))
     (setf w1 (car w))
     B2
     (setf ts s)
     (cond ((null w1) (go B5)))
     B3
     (cond ((equal (car w1) (caar ts)) (go B4)))
     (setf ts (cdr ts))
     (go B3)
     B4
     (setf u1 (cons (car ts) u1))
     (setf w1 (cdr w1))
     (go B2)
     B5
     (setf u (cons u1 u1))
     (setf w (cdr w))
     (setf u1 nil)
     (go B1)
     B6
     (setf w (reverse u))
     (setf n n1)
     (setf u (contradict s1 s2))
     (cond ((not (null u)) (return u)))
     (setf k 1)
     B7
     (cond ((> k n2) (return (quote (s is not proved)))))
     (setf ck (car s3))
     (setf wck (car w))
     (setf v (gunit s1 s2 wck ck n))
     (cond ((null (car v)) (go B12)))
     (setf n (caddr v))
     (setf hist (append hist (cadr v)))
     (setf v (car v))
     (cond ((< k n3) (go B8)))
     (setf v (ftest v n4))
     B8
     (setf v (pnsort v))
     (setf pos (stest s1 (car v)))
     (setf neg (stest s2 (cadr v)))
     (cond ((null (append pos neg)) (go B12)))
     (setf u (contradict s1 neg))
     (cond ((not (null u)) (return (dtree u hist n1))))
     (setf u (contradict pos s2))
     (cond ((not (null u)) (return (dtree u hist n1))))
     (setf s1 (append s1 pos))
     (setf s2 (append s2 neg))
     (setf w (cdr w))
     (setf y (append pos neg))
     B9
     (cond ((null w) (go B10)))
     (setf x1 (append y (car w)))
     (setf x (cons x1 x))
     (setf w (cdr w))
     (go B9)
     B10
     (setf w (append (reverse x) (list y)))
     (setf x nil)
     B11
     (setf s3 (append (cdr s3) (list ck)))
     (setf k (add1 k))
     (go B7)
     B12
     (setf w (append (cdr w) (list nil)))
     (go B11)))


;;; ------------------------------------------------------------
;;; Practical examples:


(defun example1 ()
  (tpu
   '((1 (x y) ((p (g x y) x y)))
     (2 (x y) ((p x (h x y) y))))
   '((3 (x) ((not p (k x) x (k x)))))
   '(( 4 (x y z u v w) ((not p x y u) (not p y z v) (not p x v w) (p u z w)))
     ( 5 (x y z u v w) ((not p x y u) (not p y z v) (not p u z w) (p x v w))))
   '( (3) nil)
   '5
   '2
   '3
   '0))


(defun example2 ()
  (tpu
   '((1 (x) ((p e x x)))
     (2 (x) ((p x e x)))
     (3 (x) ((p x x e)))
     (4 ()  ((p a b c))))
   '(( 5 () ((not p b a c))))
   '(( 6 (x y z u v w) ((not p x y u) (not p y z v) (not p x v w) (p u z w)))
     ( 7 (x y z u v w) ((not p x y u) (not p y z v) (not p u z w) (p x v w))))
   '( (4) nil)
   '7
   '4
   '5
   '0))


